#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Transfert de bloc-macro avec SUBSTITUTION DES ARGUMENTS-TERMES (pivot, pas 17).

Le pas 16-suite a prouvé que copier un bloc-macro d'une autre preuve + renommer les variables
Python échoue (~0 %) : les instances diffèrent au niveau TERME (littéraux comme 'x'/'y' nommant
les variables liées, objets locaux). Test DIRECT de l'hypothèse « une macro est un TEMPLATE
PARAMÉTRÉ » : on étend le transplant pour substituer AUSSI les **littéraux-chaînes** du bloc
donneur (recherche bornée sur les chaînes de la preuve cible), le noyau validant. Si le taux
BONDIT vs la baseline « variables seules », l'hypothèse est confirmée : il manquait juste la
synthèse des arguments-termes (= ce qu'un générateur appris devra produire).

On mesure côte-à-côte, sur les MÊMES blocs (donneuse ≠ P) :
  · VARIABLES seules  — renommage des ast.Name (= pas 16-suite, baseline) ;
  · VARIABLES+TERMES  — + substitution des littéraux-chaînes étrangers → chaînes locales de P.

Outillage seulement (outils_ia/) ; exécution en COPIE du namespace ; aucun Theoreme forgé ;
le noyau reste seul juge. Réutilise proto_macro_noyau.

USAGE : python outils_ia/corpus/proto_macro_termes.py [module1 module2 ...]
"""
from __future__ import annotations

import ast
import copy
import importlib
import itertools
import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from proto_mutation_verify import _cible_de, _rebuild           # noqa: E402
from gen_paires_corruption import _statut                       # noqa: E402
from proto_macro_noyau import (_proofs, _occurrences, MODULES, TEST_LOURD, NS)  # noqa: E402
from repair_learned import _assignes, _charges                  # noqa: E402
from proto_inter_preuves import _appels_noms                    # noqa: E402


class _Substitue(ast.NodeTransformer):
    """Renomme les variables (ast.Name) ET substitue les littéraux-chaînes (ast.Constant str)."""
    def __init__(self, var_map, str_map):
        self.v = var_map
        self.s = str_map

    def visit_Name(self, node):
        if node.id in self.v:
            return ast.copy_location(ast.Name(id=self.v[node.id], ctx=node.ctx), node)
        return node

    def visit_Constant(self, node):
        if isinstance(node.value, str) and node.value in self.s:
            return ast.copy_location(ast.Constant(value=self.s[node.value]), node)
        return node


def _apply(bloc, var_map, str_map):
    out = []
    for s in bloc:
        ns = _Substitue(var_map, str_map).visit(copy.deepcopy(s))
        ast.fix_missing_locations(ns)
        out.append(ns)
    return out


def _str_consts(stmts):
    """Ensemble des littéraux-chaînes (Constant str) apparaissant dans des statements."""
    out = set()
    for s in stmts:
        for n in ast.walk(s):
            if isinstance(n, ast.Constant) and isinstance(n.value, str):
                out.add(n.value)
    return out


def _var_mappings(bloc, manquantes, dispo, vars_locales, max_in=2, cap=24):
    """Mappings de VARIABLES {ancien:nouveau} : m sorties→manquantes, internes→frais, entrées→locales."""
    miss = sorted(manquantes)
    m = len(miss)
    if m == 0:
        return
    A = sorted(set().union(*[_assignes(s) for s in bloc]) & vars_locales)
    if len(A) < m:
        return
    lues = set().union(*[(_charges(s) - _appels_noms(s)) for s in bloc])
    inputs = sorted((lues & vars_locales) - set(A))
    cibles = sorted(dispo)
    if len(inputs) > max_in or len(inputs) > len(cibles):
        return
    n = 0
    for outs in itertools.permutations(A, m):
        base = dict(zip(outs, miss))
        for k, v in enumerate(v for v in A if v not in base):
            base[v] = f"_mac{k}"
        if not inputs:
            yield dict(base)
            n += 1
            if n >= cap:
                return
            continue
        for combo in itertools.permutations(cibles, len(inputs)):
            mp = dict(base)
            mp.update(dict(zip(inputs, combo)))
            yield mp
            n += 1
            if n >= cap:
                return


def _str_mappings(bloc, p_literals, cap=12):
    """Substitutions des littéraux-chaînes ÉTRANGERS du bloc → chaînes locales de P (bornées)."""
    bl = _str_consts(bloc)
    etrangers = sorted(bl - p_literals)           # chaînes absentes de P (à substituer)
    cibles = sorted(p_literals - bl)              # chaînes de P libres (pas déjà dans le bloc)
    if not etrangers:
        yield {}                                  # rien à substituer
        return
    if len(etrangers) > len(cibles):
        return
    n = 0
    for combo in itertools.permutations(cibles, len(etrangers)):
        yield dict(zip(etrangers, combo))
        n += 1
        if n >= cap:
            return


def _ctx_trou(infoP, j, L, vars_locales):
    """(cible-manquantes, dispo, abs_j) pour le bloc supprimé [j,j+L) de P."""
    fdef, body, start = infoP[0], infoP[1], infoP[2]
    abs_j = start + j
    corrompu = body[:abs_j] + body[abs_j + L:]
    assignes = set().union(*[_assignes(s) for s in corrompu]) if corrompu else set()
    lues_ap = set().union(*[_charges(s) for s in corrompu[abs_j:]]) if corrompu[abs_j:] else set()
    manquantes = (lues_ap - assignes) & vars_locales
    avant = corrompu[:abs_j]
    params = {a.arg for a in fdef.args.args}
    dispo = ((set().union(*[_assignes(s) for s in avant]) if avant else set()) | params)
    return manquantes, dispo, abs_j


def regen(mod, P, infoP, donor_bloc, j, L, vars_locales, avec_termes):
    """Régénère le bloc supprimé ; si avec_termes, substitue aussi les littéraux. Noyau OK ?"""
    fdef, body = infoP[0], infoP[1]
    cible = _cible_de(mod, P)
    manquantes, dispo, abs_j = _ctx_trou(infoP, j, L, vars_locales)
    p_literals = _str_consts(body)
    str_maps = list(_str_mappings(donor_bloc, p_literals)) if avec_termes else [{}]
    for vm in _var_mappings(donor_bloc, manquantes, dispo, vars_locales):
        for sm in str_maps:
            recon = body[:abs_j] + _apply(donor_bloc, vm, sm) + body[abs_j + L:]
            if _statut(mod, P, _rebuild(fdef, recon), cible) == "OK":
                return True
    return False


def main(argv):
    modnames = argv[1:] or MODULES
    tot = {"blocs": 0, "var": 0, "vt": 0}
    detail = []
    for modname in modnames:
        mod, proofs = _proofs(modname)
        if not proofs:
            continue
        vars_locales = {v for _, b, s, _ in proofs.values() for st in b[s:] for v in _assignes(st)}
        from collections import defaultdict
        ng_pr = defaultdict(set)
        for name, (_, _, _, sigs) in proofs.items():
            for nlen in NS:
                for i in range(len(sigs) - nlen + 1):
                    ng_pr[tuple(sigs[i:i + nlen])].add(name)
        macros = {ng for ng, pr in ng_pr.items() if len(pr) >= 2}
        court = modname.split(".")[-1]
        nb = nvar = nvt = 0
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
                nb += 1
                nvar += int(regen(mod, P, proofs[P], donor_bloc, j, L, vars_locales, False))
                nvt += int(regen(mod, P, proofs[P], donor_bloc, j, L, vars_locales, True))
        tot["blocs"] += nb
        tot["var"] += nvar
        tot["vt"] += nvt
        if nb:
            detail.append(f"  {court:<34} {nb:>3} blocs : variables seules {nvar:>3} "
                          f"({100*nvar//nb}%)  →  +termes {nvt:>3} ({100*nvt//nb}%)")
    print("# pas 17 — transfert de bloc-macro : VARIABLES seules vs VARIABLES+TERMES (noyau validant)")
    for d in detail:
        print(d)
    b = tot["blocs"]
    if b:
        print(f"\n# TOTAL {b} blocs (donneuse≠P) — variables seules {tot['var']} "
              f"({100*tot['var']//b}%)  →  +substitution des termes {tot['vt']} ({100*tot['vt']//b}%).")
        print("# Si le taux BONDIT : confirme qu'une macro est un TEMPLATE PARAMÉTRÉ — il manquait la")
        print("# synthèse des arguments-termes (ce qu'un générateur APPRIS devra produire, pas 18).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
