#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Harnais d'ATTEIGNABILITÉ dirigé-par-but — stress-test de l'IA de découverte sur des cibles DURES.

Mesure, HONNÊTEMENT, ce que le moteur de chaînage (conjecturer) peut ATTEINDRE :
  · HELD-OUT : on RETIRE un théorème clos du corpus, on lance la découverte profonde (itérée) sur le
    reste, et on regarde si l'IA le REDÉCOUVRE (clé α-canonique). C'est un test leave-one-out rigoureux :
    un corollaire chaînable DOIT être rejoint (contrôle positif) ; un théorème profond (Cantor, récurrence,
    nouvelle définition) ne le sera PAS (contrôle négatif) — et c'est le résultat qui pointe l'amélioration.
  · CIBLE FORMELLE : un énoncé qu'on FORMALISE à la main (théorème non-fait / exercice) ; on regarde si la
    découverte sur le corpus complet l'atteint.

Le noyau reste seul juge (les découvertes sont certifiées) ; frontière 22 axiomes non concernée (lecture).
USAGE : python outils_ia/corpus/eval_cibles.py [--rounds N] [--holdout m.f,m.f] [package…]
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from conjecturer import _corpus, iterer, _cle_canon, _comme_impl, _fmt, PACKAGES  # noqa: E402


def _reach_keys(impls, preuve_de, rounds):
    """Ensemble des clés α-canoniques atteintes par la découverte itérée profonde."""
    tous, par_tour = iterer(impls, preuve_de, rounds=rounds)
    prof = {}
    for t, d in enumerate(par_tour):
        for (_, _, _, thm) in d:
            prof.setdefault(_cle_canon(thm.conclusion), t + 1)          # profondeur de 1re atteinte
    return prof


def evaluer_heldout(packages, noms, rounds=3):
    """Pour chaque nom `module.func`, retire la cible et teste si l'IA la redécouvre."""
    impls, preuve_de = _corpus(packages)
    par_nom = {}
    for c, (n, thm) in preuve_de.items():
        par_nom.setdefault(n, (c, thm))
    res = []
    for nom in noms:
        if nom not in par_nom:
            res.append((nom, "ABSENT", None, None))
            continue
        concl, _ = par_nom[nom]
        cle = _cle_canon(concl)
        impls2 = [x for x in impls if x[0] != nom]
        preuve2 = {c: v for c, v in preuve_de.items() if v[0] != nom}
        prof = _reach_keys(impls2, preuve2, rounds)
        atteint = cle in prof
        res.append((nom, "ATTEINT" if atteint else "NON ATTEINT",
                    prof.get(cle), _fmt(concl)))
    return res


def evaluer_formelles(packages, cibles, rounds=3):
    """cibles = [(label, conclusion_Formule)] : test d'atteignabilité sur le corpus complet."""
    impls, preuve_de = _corpus(packages)
    prof = _reach_keys(impls, preuve_de, rounds)
    res = []
    for (label, concl) in cibles:
        cle = _cle_canon(concl)
        res.append((label, "ATTEINT" if cle in prof else "NON ATTEINT",
                    prof.get(cle), _fmt(concl)))
    return res


def _tableau(titre, res):
    print(f"\n# {titre}")
    print(f"#  {'cible':<48} {'verdict':<12} prof.")
    n_ok = 0
    for (nom, verdict, prof, enonce) in res:
        n_ok += verdict == "ATTEINT"
        p = str(prof) if prof else "-"
        print(f"#  {nom[:48]:<48} {verdict:<12} {p}")
    tot = len(res)
    print(f"#  → {n_ok}/{tot} atteints")
    return n_ok, tot


def main(argv):
    rest = argv[1:]
    rounds = 3
    holdout = []
    if "--rounds" in rest:
        i = rest.index("--rounds"); rounds = int(rest[i + 1]); rest = rest[:i] + rest[i + 2:]
    if "--holdout" in rest:
        i = rest.index("--holdout"); holdout = rest[i + 1].split(","); rest = rest[:i] + rest[i + 2:]
    packages = [a for a in rest if not a.startswith("--")] or PACKAGES

    print(f"# HARNAIS D'ATTEIGNABILITÉ — rounds={rounds}, packages={packages}", file=sys.stderr)
    if not holdout:
        # smoke : auto-choisir 3 implications du corpus comme held-out (mécanique)
        impls, preuve_de = _corpus(packages)
        holdout = [x[0] for x in impls[:3]]
        print(f"# (démo) held-out auto : {holdout}", file=sys.stderr)
    res = evaluer_heldout(packages, holdout, rounds=rounds)
    _tableau(f"HELD-OUT (retiré du corpus → l'IA le redécouvre-t-elle ?)", res)
    print("\n# ATTEINT = corollaire re-dérivable par chaînage ; NON ATTEINT = hors de portée du chaînage")
    print("# (exige lemmes/définitions/induction) → c'est là que le stress-test pointe l'amélioration.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
