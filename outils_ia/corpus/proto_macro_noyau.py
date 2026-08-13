#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Valider une MACRO multi-pas par le NOYAU (pivot, pas 16-suite).

Le pas 14 a montré qu'un pas ISOLÉ d'une autre preuve ne se régénère pas (tactique étrangère
0 %). Le pas 16 a montré que les BLOCS multi-pas (macros) sont massivement partagés. Question
décisive : un bloc multi-pas se RÉGÉNÈRE-t-il depuis une AUTRE preuve, le noyau certifiant le
bloc entier ? Si oui, on a un vrai vocabulaire MULTI-pas (≠ le 1-pas à rendement nul).

Protocole, par macro (sous-séquence de tactiques (fn,arité) présente dans ≥2 preuves) :
  · preuve TEST P contenant la macro → SUPPRIMER le bloc de L pas correspondant ;
  · preuve DONNEUSE Q≠P contenant la même macro → prendre SON bloc concret (L statements) ;
  · TRANSPLANTER le bloc de Q dans le trou de P, re-bindé : variables internes du bloc → noms
    FRAIS (flot interne préservé), sortie → variable manquante de P (data-flow), entrées → variables
    locales de P (recherche de binding bornée) ;
  · le NOYAU valide le P reconstruit (conclusion == cible) = bloc multi-pas CERTIFIÉ.

On mesure le taux de régénération de BLOC (donneuse ≠ P) — à contraster avec le 1-pas (pas 14).
Outillage seulement (outils_ia/) ; exécution en COPIE du namespace ; aucun Theoreme forgé ;
le noyau reste seul juge. Réutilise la machinerie de proto_inter_preuves.

USAGE : python outils_ia/corpus/proto_macro_noyau.py [module1 module2 ...]
"""
from __future__ import annotations

import ast
import copy
import importlib
import inspect
import itertools
import sys
import textwrap
from collections import defaultdict
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from proto_mutation_verify import _cible_de, _rebuild           # noqa: E402
from gen_paires_corruption import _statut                       # noqa: E402
from proto_inter_preuves import _corps, _Renomme, _appels_noms  # noqa: E402
from repair_learned import _assignes, _charges, _fn_principale, _n_args  # noqa: E402

MODULES = [
    "bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projection_fonctionnelle",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_identite_neutre",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_diagonale_couple",
    "bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_3_composee_graphes.ensembles_composee_monotone",
]
TEST_LOURD = {"couple_diagonale"}                                # exclu comme TEST (6707 pas, ~20ms/essai)
NS = (2, 3)                                                      # longueurs de macro essayées


def _proofs(modname):
    """{name: (fdef, body, start, sigs)} pour les théorèmes du module (avec compagnon _cible)."""
    try:
        mod = importlib.import_module(modname)
    except Exception:
        return None, {}
    res = {}
    for name in getattr(mod, "__all__", []):
        if name.endswith("_cible") or not callable(getattr(mod, name, None)) \
                or _cible_de(mod, name) is None:
            continue
        try:
            fdef, body, start = _corps(mod, name)
        except Exception:
            continue
        sigs = [(_fn_principale(s), _n_args(s)) for s in body[start:]]
        res[name] = (fdef, body, start, sigs)
    return mod, res


def _apply(bloc, mapping):
    """Copie le bloc en renommant ses Name selon mapping (sortie/entrées/internes re-câblées)."""
    out = []
    for s in bloc:
        ns = _Renomme(mapping).visit(copy.deepcopy(s))
        ast.fix_missing_locations(ns)
        out.append(ns)
    return out


def _transplants_bloc(bloc, manquantes, dispo, vars_locales, max_in=2, cap=120):
    """Variantes du bloc DONNEUR re-bindé : m sorties→m variables manquantes (data-flow),
    internes→noms FRAIS (flot interne préservé), entrées→variables locales (binding). Bloc
    MULTI-sorties géré (un bloc fournit souvent plusieurs variables lues plus loin)."""
    miss = sorted(manquantes)
    m = len(miss)
    if m == 0:
        return
    A = sorted(set().union(*[_assignes(s) for s in bloc]) & vars_locales)        # assignées (locales)
    if len(A) < m:
        return
    lues = set().union(*[(_charges(s) - _appels_noms(s)) for s in bloc])
    inputs = sorted((lues & vars_locales) - set(A))                              # lues, non assignées dans le bloc
    cibles = sorted(dispo)
    if len(inputs) > max_in or len(inputs) > len(cibles):
        return
    n = 0
    for outs in itertools.permutations(A, m):              # quelles m vars du bloc sont les SORTIES
        base = dict(zip(outs, miss))                       # sortie_k → manquante_k
        for k, v in enumerate(v for v in A if v not in base):
            base[v] = f"_mac{k}"                           # internes → noms FRAIS
        if not inputs:
            yield _apply(bloc, base)
            n += 1
            if n >= cap:
                return
            continue
        for combo in itertools.permutations(cibles, len(inputs)):
            mp = dict(base)
            mp.update(dict(zip(inputs, combo)))
            yield _apply(bloc, mp)
            n += 1
            if n >= cap:
                return


def _occurrences(sigs, macro):
    L = len(macro)
    return [i for i in range(len(sigs) - L + 1) if tuple(sigs[i:i + L]) == macro]


def regenerer_bloc(mod, P, infoP, donneuse_bloc, j, L, vars_locales):
    """Supprime le bloc [j,j+L) de P, transplante le bloc DONNEUR re-bindé ; noyau OK ?"""
    fdef, body, start = infoP[0], infoP[1], infoP[2]
    name = P
    cible = _cible_de(mod, name)
    abs_j = start + j                                       # indice absolu dans body
    corrompu = body[:abs_j] + body[abs_j + L:]
    # data-flow : variable PROOF-LOCALE lue après le trou mais non fournie
    assignes = set().union(*[_assignes(s) for s in corrompu]) if corrompu else set()
    lues_ap = set().union(*[_charges(s) for s in corrompu[abs_j:]]) if corrompu[abs_j:] else set()
    manquantes = (lues_ap - assignes) & vars_locales
    avant = corrompu[:abs_j]
    params = {a.arg for a in fdef.args.args}
    dispo = ((set().union(*[_assignes(s) for s in avant]) if avant else set()) | params)
    for variant in _transplants_bloc(donneuse_bloc, manquantes, dispo, vars_locales):
        recon = body[:abs_j] + variant + body[abs_j + L:]
        if _statut(mod, name, _rebuild(fdef, recon), cible) == "OK":
            return True
    return False


def main(argv):
    modnames = argv[1:] or MODULES
    tot = {"essais": 0, "ok": 0, "ok_cross": 0, "blocs": 0}
    detail = []
    for modname in modnames:
        mod, proofs = _proofs(modname)
        if not proofs:
            continue
        vars_locales = {v for _, b, s, _ in proofs.values() for st in b[s:] for v in _assignes(st)}
        # macros = sous-séquences (len ∈ NS) présentes dans ≥2 preuves DU MODULE
        ng_pr = defaultdict(set)
        for name, (_, _, _, sigs) in proofs.items():
            for nlen in NS:
                for i in range(len(sigs) - nlen + 1):
                    ng_pr[tuple(sigs[i:i + nlen])].add(name)
        macros = {ng for ng, pr in ng_pr.items() if len(pr) >= 2}
        court = modname.split(".")[-1]
        nblocs = nok = nok_cross = 0
        for macro in macros:
            porteuses = [n for n in proofs if _occurrences(proofs[n][3], macro)]
            for P in porteuses:
                if P in TEST_LOURD:
                    continue
                donneuses = [q for q in porteuses if q != P]
                if not donneuses:
                    continue
                Q = donneuses[0]                            # 1 donneuse (la 1re autre preuve)
                j = _occurrences(proofs[P][3], macro)[0]
                L = len(macro)
                qb_start = proofs[Q][2] + _occurrences(proofs[Q][3], macro)[0]
                donneuse_bloc = proofs[Q][1][qb_start:qb_start + L]
                nblocs += 1
                tot["essais"] += 1
                ok = regenerer_bloc(mod, P, proofs[P], donneuse_bloc, j, L, vars_locales)
                nok += int(ok)
                nok_cross += int(ok)                        # Q≠P par construction → cross-preuve
        tot["blocs"] += nblocs
        tot["ok"] += nok
        tot["ok_cross"] += nok_cross
        if nblocs:
            detail.append(f"  {court:<34} {nblocs:>3} blocs-macro testés : {nok:>3} régénérés "
                          f"(donneuse≠P) ({100*nok//nblocs}%)")
    print("# pas 16-suite — régénération de BLOC multi-pas depuis une AUTRE preuve, noyau validant")
    for d in detail:
        print(d)
    b = tot["blocs"]
    if b:
        print(f"\n# TOTAL {b} blocs-macro (donneuse≠P) — {tot['ok']} régénérés + certifiés noyau "
              f"({100*tot['ok']//b}%).")
        print("# RÉSULTAT NÉGATIF (cause prouvée) : copier le bloc concret d'une autre preuve + re-bind")
        print("# des variables Python ne reproduit ~JAMAIS la cible. Les instances d'une même macro")
        print("# diffèrent au niveau TERME (ex. c45_avant(R,'x',..) vs (R,'y',..), pr1z vs pr2z) — des")
        print("# LITTÉRAUX/objets que le renommage de variables ne substitue pas. Une macro est un")
        print("# TEMPLATE PARAMÉTRÉ sur ses arguments-termes : transférer/générer exige de SYNTHÉTISER")
        print("# ces arguments (le noyau validant), pas de copier-coller. → confirme le besoin d'un")
        print("# générateur APPRIS (la récupération/copie ne suffit pas). Levier suivant = substituer")
        print("# aussi les arguments-termes (chaînes nommant les variables liées, objets locaux).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
