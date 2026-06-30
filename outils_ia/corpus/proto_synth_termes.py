#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""SYNTHÈSE de termes bornée : GÉNÉRER les arguments d'une macro, pas les copier (pivot, pas 18).

Le pas 17 a prouvé que les arguments d'une macro sont des SOUS-TERMES STRUCTURÉS (arbres
d'expression) → la substitution d'atomes plafonne à ~5 %. Ici on franchit le pas : pour un
bloc-macro supprimé, on garde le SQUELETTE (les appels-tactiques du donneur = la signature
de la macro) mais on SYNTHÉTISE les slots-termes depuis le vocabulaire LOCAL de P :
  atomes = variables locales de P + var('<noms liés de P>') ;
  constructeurs = E.composee/2, E.diagonale/1, E.couple/2 (+ var/1), appliqués à profondeur ≤2.
On remplit les slots, le NOYAU filtre. C'est la 1re vraie GÉNÉRATION (on construit des termes
adaptés à P, on ne recopie pas ceux du donneur) — à comparer au plafond 5 % de la copie (pas 17).

Outillage seulement (outils_ia/) ; exécution en COPIE du namespace ; aucun Theoreme forgé ;
le noyau reste seul juge. Réutilise proto_macro_noyau / proto_macro_termes.

USAGE : python outils_ia/corpus/proto_synth_termes.py [module1 module2 ...]
"""
from __future__ import annotations

import ast
import copy
import importlib
import itertools
import sys
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
from proto_macro_noyau import _proofs, _occurrences, TEST_LOURD, NS  # noqa: E402
from proto_macro_termes import _str_consts, _var_mappings, _ctx_trou          # noqa: E402
from repair_learned import _assignes, _charges                  # noqa: E402
from proto_inter_preuves import _appels_noms                    # noqa: E402

MAXT = 400               # plafond du pool de termes synthétisés
MAX_SLOTS = 2            # blocs avec ≤ MAX_SLOTS slots-termes (sinon trop combinatoire)
CAP_COMBOS = 4000        # plafond dur d'essais-noyau par bloc (l'énumération depth-2 explose : voir pas 19)
PROF = 3                 # profondeur de synthèse (3 = 2 tours de constructeurs → termes imbriqués)

# défaut = module RAPIDE (projection, ~1.3 ms/essai) qui DÉMONTRE la synthèse end-to-end ; les
# modules à slots PROFONDS (identite/diagonale, terme-oracle au rang ~561/7265) exigent le prior
# appris (pas 19) — les passer en argument explicite + gros budget si besoin.
DEFAUT = ["bourbaki.ensembles.ii_2_couples_produit.ensembles_projection_fonctionnelle"]


def _name(s):
    return ast.Name(id=s, ctx=ast.Load())


def _attr_call(obj, meth, args):
    return ast.Call(func=ast.Attribute(value=ast.Name(id=obj, ctx=ast.Load()), attr=meth,
                                       ctx=ast.Load()), args=list(args), keywords=[])


def _fn_call(fn, args):
    return ast.Call(func=ast.Name(id=fn, ctx=ast.Load()), args=list(args), keywords=[])


def synth_termes(var_atoms, str_atoms, prof=PROF):
    """Énumère des termes depuis le vocabulaire local de P (profondeur ≤ prof), borné à MAXT.
    Chaque tour combine TOUS les niveaux accumulés (pas seulement le précédent) → génère aussi
    les termes de profondeur mixte (ex. composee(atome, diagonale(atome)))."""
    base = ([_name(v) for v in sorted(var_atoms)]
            + [_fn_call("var", [ast.Constant(s)]) for s in sorted(str_atoms)]
            # pas 23 : noms de variables liées en LITTÉRAUX nus ('y', 'w'…) — slots des primitives
            # s5/s6/symetrie/existe_temoin qui prennent une chaîne-nom (49 slots/243 hors grammaire).
            + [ast.Constant(s) for s in sorted(str_atoms)])
    pool = list(base)
    vus = {ast.dump(t) for t in pool}

    def _ajoute(t):
        d = ast.dump(t)
        if d not in vus:
            vus.add(d)
            pool.append(t)

    for _ in range(prof - 1):
        src = list(pool)                                        # UNION de tous les niveaux
        for a in src:                                           # diagonale/1
            _ajoute(_attr_call("E", "diagonale", [a]))
        for a, b in itertools.product(src, repeat=2):           # composee/2, couple/2
            _ajoute(_attr_call("E", "composee", [a, b]))
            _ajoute(_attr_call("E", "couple", [a, b]))
            if len(pool) > 6 * MAXT:
                break
        if len(pool) >= MAXT:
            break
    # pas 24-25 : COUCHE FORMULES/PREUVE sur atomes-Name (NON réinjectée dans la couche objets →
    # pas d'explosion ; args = vraies variables data-flow → le TreeNN les distingue ≠ littéraux nus).
    # Construite à PART avec QUOTA réservé (sinon l'explosion objet la tronque, elle est tardive) :
    #  · pas 24 : et/2 (formules nommées, ex. et(P, Gxz)) ;
    #  · pas 25 : inclus/2 (relations) + conjonction_elim_gauche/droite (proof-terms unaires, ex.
    #    conjonction_elim_gauche(ha) — 19 slots hors grammaire des modules à couples/produit).
    noms = [_name(v) for v in sorted(var_atoms)]
    forms = []

    def _aj_form(t):
        d = ast.dump(t)
        if d not in vus:
            vus.add(d)
            forms.append(t)

    for fn in ("conjonction_elim_gauche", "conjonction_elim_droite"):  # proof-terms unaires (cheap)
        for a in noms:
            _aj_form(_fn_call(fn, [a]))
    for a, b in itertools.product(noms, repeat=2):                     # binaires Name×Name
        _aj_form(_fn_call("inclus", [a, b]))
        _aj_form(_fn_call("et", [a, b]))
    qf = min(len(forms), max(1, MAXT // 3))                            # réserve ≤ 1/3 du budget
    return pool[:MAXT - qf] + forms[:qf]


def _slots(call):
    """Positions d'arguments NON-triviaux (slots-termes) d'un Call : tout sauf un ast.Name nu."""
    return [k for k, a in enumerate(call.args) if not isinstance(a, ast.Name)]


def regen_synth(mod, P, infoP, donor_bloc, j, L, vars_locales, pool):
    """Garde le squelette (appels du donneur), SYNTHÉTISE les slots-termes ; noyau OK ?"""
    fdef, body = infoP[0], infoP[1]
    cible = _cible_de(mod, P)
    manquantes, dispo, abs_j = _ctx_trou(infoP, j, L, vars_locales)
    # nb de slots-termes du bloc (arguments non-triviaux des Call de 1er niveau)
    nslots = 0
    for st in donor_bloc:
        call = None
        for n in ast.walk(st):
            if isinstance(n, ast.Call):
                call = n
                break
        if call is not None:
            nslots += len(_slots(call))
    if nslots == 0 or nslots > MAX_SLOTS:
        return None                                            # rien à synthétiser / trop combinatoire
    n_essais = 0
    for vm in _var_mappings(donor_bloc, manquantes, dispo, vars_locales, cap=6):
        grilles = itertools.product(pool, repeat=nslots)
        for grille in grilles:
            bloc = []
            gi = 0
            ok_build = True
            for st in donor_bloc:
                ns = copy.deepcopy(st)
                # appliquer le mapping de variables (squelette + sorties/entrées)
                for node in ast.walk(ns):
                    if isinstance(node, ast.Name) and node.id in vm:
                        node.id = vm[node.id]
                # remplir les slots de CE statement
                call = None
                for node in ast.walk(ns):
                    if isinstance(node, ast.Call):
                        call = node
                        break
                if call is not None:
                    for k in _slots(call):
                        if gi >= len(grille):
                            ok_build = False
                            break
                        call.args[k] = copy.deepcopy(grille[gi])
                        gi += 1
                ast.fix_missing_locations(ns)
                bloc.append(ns)
            if not ok_build:
                continue
            recon = body[:abs_j] + bloc + body[abs_j + L:]
            n_essais += 1
            if _statut(mod, P, _rebuild(fdef, recon), cible) == "OK":
                return True
            if n_essais >= CAP_COMBOS:
                return False
    return False


def main(argv):
    modnames = argv[1:] or DEFAUT
    tot = {"blocs": 0, "synth": 0, "testables": 0}
    detail = []
    for modname in modnames:
        mod, proofs = _proofs(modname)
        if not proofs:
            continue
        vars_locales = {v for _, b, s, _ in proofs.values() for st in b[s:] for v in _assignes(st)}
        ng_pr = defaultdict(set)
        for name, (_, _, _, sigs) in proofs.items():
            for nlen in NS:
                for i in range(len(sigs) - nlen + 1):
                    ng_pr[tuple(sigs[i:i + nlen])].add(name)
        macros = {ng for ng, pr in ng_pr.items() if len(pr) >= 2}
        court = modname.split(".")[-1]
        nb = ntest = nok = 0
        for macro in macros:
            porteuses = [n for n in proofs if _occurrences(proofs[n][3], macro)]
            for P in porteuses:
                if P in TEST_LOURD:
                    continue
                donneuses = [q for q in porteuses if q != P]
                if not donneuses:
                    continue
                Q = donneuses[0]
                j = _occurrences(proofs[P][3], macro)[0]
                L = len(macro)
                qb = proofs[Q][2] + _occurrences(proofs[Q][3], macro)[0]
                donor_bloc = proofs[Q][1][qb:qb + L]
                # vocabulaire LOCAL de P : variables-atomes (toutes locales + params) + noms-chaînes
                # courts (noms de variables liées ; on EXCLUT la docstring & les longues chaînes).
                fdef, body, start, _ = proofs[P]
                params = {a.arg for a in fdef.args.args}
                var_atoms = ({v for st in body[start:] for v in _assignes(st)} | params)
                str_atoms = {s for s in _str_consts(body) if s.isidentifier() and len(s) <= 3}
                pool = synth_termes(var_atoms, str_atoms)
                nb += 1
                r = regen_synth(mod, P, proofs[P], donor_bloc, j, L, vars_locales, pool)
                if r is None:
                    continue
                ntest += 1
                nok += int(r)
        tot["blocs"] += nb
        tot["testables"] += ntest
        tot["synth"] += nok
        if ntest:
            detail.append(f"  {court:<34} {ntest:>3} blocs synthétisables (≤{MAX_SLOTS} slots) : "
                          f"{nok:>3} régénérés par SYNTHÈSE ({100*nok//ntest}%)")
    print("# pas 18 — GÉNÉRATION : synthèse des slots-termes depuis le vocabulaire local (noyau validant)")
    for d in detail:
        print(d)
    t = tot["testables"]
    if t:
        print(f"\n# TOTAL {tot['blocs']} blocs ({t} avec ≤{MAX_SLOTS} slots-termes) — "
              f"{tot['synth']} régénérés par SYNTHÈSE de termes locaux ({100*tot['synth']//t}%).")
        print("# À COMPARER au plafond 5 % de la COPIE (pas 17) : si > 5 %, on GÉNÈRE des termes")
        print("# adaptés à P (pas une recopie) = le cœur generate-and-verify multi-pas. pas 19 =")
        print("# prior APPRIS sur la synthèse (ranger les termes candidats → moins d'essais-noyau).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
