#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Bibliothèque INTER-preuves : réparer depuis un vocabulaire PARTAGÉ (pivot, pas 14).

Jusqu'ici la « bibliothèque » candidate = les pas de la preuve COURANTE seulement
(proto_repair, repair_learned, proto_sequential). C'est recombiner UNE preuve, pas
générer. Ici on construit un POOL PARTAGÉ : tous les pas de TOUTES les preuves du module.
On mesure alors si un trou peut être comblé par un pas venu d'une AUTRE preuve — c'est le
1er pas vers générer depuis un vocabulaire commun (pas juste permuter une trajectoire).

Deux régimes de transplant d'un candidat étranger :
  · VERBATIM      — on ré-insère le pas tel quel (ne marche que si les variables coïncident) ;
  · TRANSPLANTÉ   — on renomme l'unique cible d'affectation du candidat vers l'unique
                    variable MANQUANTE du trou (data-flow) : le pas étranger « fournit » la
                    bonne variable locale. Le NOYAU reste l'oracle exact (OK == cible).

Trois mesures, par trou (suppression 1-pas) :
  · récupérable LOCAL     — l'oracle (pool de la preuve elle-même) répare (doit être ~100 %) ;
  · réparé CROSS-verbatim — un pas d'une AUTRE preuve, tel quel, répare (vocabulaire commun
                            quand les noms coïncident — ex. pas IDENTIQUES partagés) ;
  · réparé CROSS-transplant— un pas d'une autre preuve, sa sortie renommée, répare.

Outillage seulement (outils_ia/) ; exécution en COPIE du namespace ; aucun Theoreme forgé ;
le noyau reste seul juge. Réutilise la machinerie des protos.

USAGE : python outils_ia/corpus/proto_inter_preuves.py [module1 module2 ...]
"""
from __future__ import annotations

import ast
import copy
import importlib
import inspect
import itertools
import sys
import textwrap
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from proto_mutation_verify import _cible_de, _rebuild       # noqa: E402
from gen_paires_corruption import _statut                   # noqa: E402
from repair_learned import _assignes, _charges, _fn_principale, _n_args  # noqa: E402

MODULES = [
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_diagonale_couple",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_identite_neutre",
]


def _corps(mod, name):
    """(fdef, body, start) d'une fonction-théorème ; saute la docstring."""
    fdef = ast.parse(textwrap.dedent(inspect.getsource(getattr(mod, name)))).body[0]
    body = fdef.body
    start = 1 if (body and isinstance(body[0], ast.Expr)
                  and isinstance(getattr(body[0], "value", None), ast.Constant)) else 0
    return fdef, body, start


def _theoremes(mod):
    return [n for n in getattr(mod, "__all__", [])
            if not n.endswith("_cible") and callable(getattr(mod, n, None))
            and _cible_de(mod, n) is not None]


def pool_partage(mod, names):
    """Tous les pas de TOUTES les preuves du module : liste (origine, stmt), dédupe par dump."""
    pool, vus = [], set()
    for name in names:
        try:
            _, body, start = _corps(mod, name)
        except Exception:
            continue
        for s in body[start:]:
            d = ast.dump(s)
            if d not in vus:
                vus.add(d)
                pool.append((name, s))
    return pool


def vocabulaire(pool):
    """Vocabulaire PARTAGÉ = (tactique, arité) DISTINCTES sur tout le module, 1 repr. AST chacun.
    C'est la bibliothèque de TEMPLATES dont on génère un pas (pas la liste brute des statements)."""
    vus, tmpl = set(), []
    for origine, s in pool:
        if len(_assignes(s)) != 1:                            # on transplante des pas à 1 sortie
            continue
        sig = (_fn_principale(s), _n_args(s))
        if sig not in vus:
            vus.add(sig)
            tmpl.append((origine, s))
    return tmpl


class _Renomme(ast.NodeTransformer):
    """Renomme les Name selon un mapping {ancien: nouveau}."""
    def __init__(self, mapping):
        self.m = mapping

    def visit_Name(self, node):
        if node.id in self.m:
            return ast.copy_location(ast.Name(id=self.m[node.id], ctx=node.ctx), node)
        return node


def _appels_noms(stmt) -> set:
    """Noms utilisés comme FONCTION appelée (à NE PAS re-lier : ce sont des tactiques/helpers)."""
    return {n.func.id for n in ast.walk(stmt)
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)}


def _transplants(cand, manquantes, dispo, vars_locales, max_lier=2, cap=8):
    """Variantes d'un TEMPLATE étranger : sortie→variable manquante, lectures re-liées aux
    variables LOCALES disponibles (recherche de binding, le noyau filtrant). Generate-and-verify.

    On ne re-lie QUE les variables proof-locales (∈ vars_locales) : les noms de tactiques/
    helpers/`N` (jamais assignés) restent intacts. Bornes : ≤`max_lier` lectures re-liées,
    ≤`cap` variantes (coût = ré-exécution noyau de la preuve par variante)."""
    asg = list(_assignes(cand))
    if len(asg) != 1 or len(manquantes) != 1:
        return
    sortie_map = {asg[0]: next(iter(manquantes))}
    # variables LUES par le template à re-lier : proof-locales, hors sa propre sortie et hors appels
    lues = (_charges(cand) - set(asg) - _appels_noms(cand)) & vars_locales
    a_lier = sorted(v for v in lues if v not in dispo)        # déjà-dispo gardées telles quelles
    cibles = sorted(dispo)
    if not a_lier:                                            # juste la sortie à renommer
        new = _Renomme(sortie_map).visit(copy.deepcopy(cand))
        ast.fix_missing_locations(new)
        yield new
        return
    if len(a_lier) > max_lier or len(a_lier) > len(cibles):
        return
    n = 0
    for combo in itertools.permutations(cibles, len(a_lier)):  # injections lectures→locales
        mapping = dict(sortie_map)
        mapping.update(dict(zip(a_lier, combo)))
        new = _Renomme(mapping).visit(copy.deepcopy(cand))
        ast.fix_missing_locations(new)
        yield new
        n += 1
        if n >= cap:
            return


def analyse(mod, name, pool, vocab, vars_locales):
    """Pour chaque suppression 1-pas : qui répare ? (local / cross-verbatim / cross-transplant)."""
    cible = _cible_de(mod, name)
    fdef, body, start = _corps(mod, name)
    propres = {ast.dump(s) for s in body[start:]}             # pas de CETTE preuve (pour cross ≠ local)
    propres_sigs = {(_fn_principale(s), _n_args(s)) for s in body[start:]}  # tactiques de CETTE preuve
    params = {a.arg for a in fdef.args.args}
    # templates ÉTRANGERS d'abord (signature absente de la preuve courante) = vocabulaire genuinement
    # importé ; permet de mesurer si un trou se comble avec une tactique que la preuve n'a PAS.
    vocab = sorted(vocab, key=lambda ov: (_fn_principale(ov[1]), _n_args(ov[1])) in propres_sigs)
    res = {"del": 0, "local": 0, "cross_verb": 0, "cross_trans": 0, "trans_etranger": 0,
           "identiques": 0, "essais": 0}
    for i in range(start, len(body)):
        deleted = body[i]
        corrompu = body[:i] + body[i + 1:]
        # data-flow : variable lue après le trou mais non assignée ailleurs = ce qu'il faut fournir
        assignes_tous = set().union(*(_assignes(s) for s in corrompu)) if corrompu else set()
        lues_apres = set().union(*(_charges(s) for s in corrompu[i:])) if corrompu[i:] else set()
        # variable PROOF-LOCALE lue après mais non fournie = ce que le pas supprimé fournissait
        # (intersection avec vars_locales : exclut les noms de tactiques/helpers, lus mais jamais assignés)
        manquantes = (lues_apres - assignes_tous) & vars_locales
        # variables LOCALES disponibles AVANT le trou (cibles de re-liaison des lectures) + params
        avant = corrompu[:i]
        dispo = (set().union(*(_assignes(s) for s in avant)) if avant else set()) | params
        oracle_dump = ast.dump(deleted)
        local_ok = cross_verb_ok = cross_trans_ok = False
        # 1) VERBATIM : un pas d'une autre preuve, tel quel (réutilisation exacte)
        for origine, cand in pool:
            cdump = ast.dump(cand)
            est_local = cdump in propres
            essai = corrompu[:i] + [cand] + corrompu[i:]
            res["essais"] += 1
            if _statut(mod, name, _rebuild(fdef, essai), cible) == "OK":
                if cdump == oracle_dump:
                    local_ok = True
                if not est_local:
                    cross_verb_ok = True
                    if cdump == oracle_dump:
                        res["identiques"] += 1            # pas IDENTIQUE partagé entre 2 preuves
        # 2) TRANSPLANT : générer le pas depuis le VOCABULAIRE de templates partagé + binding.
        # Plafond DUR d'essais/trou (le pire-cas domine quand le transplant échoue) : budget borné.
        budget = 80
        trans_etranger_ok = False
        for origine, tmpl in vocab:                            # vocab trié : étrangers d'abord
            if cross_trans_ok or budget <= 0:
                break
            tmpl_etranger = (_fn_principale(tmpl), _n_args(tmpl)) not in propres_sigs
            for t in _transplants(tmpl, manquantes, dispo, vars_locales):
                res["essais"] += 1
                budget -= 1
                essai_t = corrompu[:i] + [t] + corrompu[i:]
                if _statut(mod, name, _rebuild(fdef, essai_t), cible) == "OK":
                    cross_trans_ok = True
                    trans_etranger_ok = tmpl_etranger    # tactique ABSENTE de la preuve courante
                    break
                if budget <= 0:
                    break
        res["del"] += 1
        res["local"] += int(local_ok)
        res["cross_verb"] += int(cross_verb_ok)
        res["cross_trans"] += int(cross_verb_ok or cross_trans_ok)
        res["trans_etranger"] += int(trans_etranger_ok)
    return res


def main(argv):
    modnames = argv[1:] or MODULES
    tot = {"del": 0, "local": 0, "cross_verb": 0, "cross_trans": 0, "trans_etranger": 0,
           "identiques": 0, "essais": 0}
    for modname in modnames:
        try:
            mod = importlib.import_module(modname)
        except Exception as e:
            print(f"# SKIP {modname} ({type(e).__name__})", file=sys.stderr)
            continue
        names = _theoremes(mod)
        pool = pool_partage(mod, names)
        vocab = vocabulaire(pool)                                   # templates (tactique, arité) distincts
        vars_locales = {v for _, s in pool for v in _assignes(s)}   # variables proof-locales du module
        print(f"\n# {modname.split('.')[-1]} — {len(names)} preuves, "
              f"pool PARTAGÉ = {len(pool)} pas distincts, vocabulaire = {len(vocab)} templates",
              flush=True)
        for name in names:
            try:
                r = analyse(mod, name, pool, vocab, vars_locales)
            except Exception as e:
                print(f"  {name:<34} SKIP ({type(e).__name__})")
                continue
            for k in tot:
                tot[k] += r[k]
            print(f"  {name:<34} {r['del']:>2} trous : "
                  f"local {r['local']:>2} | cross-verbatim {r['cross_verb']:>2} "
                  f"| template-transplant {r['cross_trans']:>2} (dont tactique étrangère "
                  f"{r['trans_etranger']:>2})", flush=True)
    if tot["del"]:
        d = tot["del"]
        print(f"\n# TOTAL {d} trous — local {tot['local']} ({100*tot['local']//d}%) | "
              f"VERBATIM (pas étranger tel quel) {tot['cross_verb']} ({100*tot['cross_verb']//d}%) | "
              f"TEMPLATE-TRANSPLANT {tot['cross_trans']} ({100*tot['cross_trans']//d}%) "
              f"dont tactique ÉTRANGÈRE {tot['trans_etranger']} ({100*tot['trans_etranger']//d}%) "
              f"| {tot['essais']} essais")
        print("# Lecture : le pas littéral d'une autre preuve ne transfère PAS (verbatim ~0 % : les")
        print("#   variables diffèrent) ; mais le pas se RÉGÉNÈRE depuis le vocabulaire de TEMPLATES")
        print("#   (tactique + recherche de binding local), le noyau validant = générer depuis un")
        print("#   vocabulaire PARTAGÉ, pas permuter une preuve. « tactique étrangère » = la signature")
        print("#   employée est ABSENTE de la preuve courante (vocabulaire genuinement importé).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
