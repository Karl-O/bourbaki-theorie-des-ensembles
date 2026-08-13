#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Fécondité prospective — extrait de `conjecturer.py` (discipline ≤300 lignes, 8 août 2026).

Générativité d'un théorème dans le DAG de découverte : combien de découvertes en
AVAL le chaînent. Signal distinct de MDL (fréquence passée) et de l'intérêt
(parcimonie) — cf. front-ouvert #1/#2 dans CAMPAGNE_TROUS.md. Imports du moteur
PARESSEUX (évite le cycle conjecturer ⇄ conj_fecondite : `conjecturer.py`
ré-exporte `fecondite` en fin de module pour ses consommateurs historiques).
"""
from __future__ import annotations

import sys
from collections import defaultdict
from pathlib import Path

_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from conj_base import _interet, _fmt                                  # noqa: E402


def fecondite(impls, preuve_de, rounds=3, garder=40):
    """Signal de FÉCONDITÉ prospectif (front-ouvert) : générativité d'un théorème dans le DAG de
    découverte = combien de découvertes en AVAL le chaînent (directement, sur `rounds` tours).

    C'est le signal que MDL et « intérêt » n'ont PAS : un lemme-clé peut apparaître UNE fois (MDL nul)
    mais engendrer tout un sous-arbre de conséquences → fécond. On mesure l'usage de chaque source
    (théorème du corpus OU brique découverte `D<t>#k`) comme parent d'une découverte.
    Renvoie (usage {nom_source: nb}, info {nom_brique: (thm, mode, s1, s2)})."""
    from conjecturer import conjecturer, _comme_impl
    pool, connus = list(impls), dict(preuve_de)
    usage, info = defaultdict(int), {}
    for t in range(rounds):
        d = conjecturer(pool, connus)
        for (_, s1, s2, _) in d:
            usage[s1] += 1
            usage[s2] += 1
        if not d or t == rounds - 1:
            break
        for k, (_, _, _, thm) in enumerate(d):
            connus.setdefault(thm.conclusion, (f"D{t + 1}#{k}", thm))
        briques = sorted((x for x in d if _comme_impl(x[3].conclusion) is not None),
                         key=lambda x: _interet(*x), reverse=True)
        for k, (m, s1, s2, thm) in enumerate(briques[:garder]):
            nom = f"D{t + 1}#{k}"
            ab = _comme_impl(thm.conclusion)
            pool.append((nom, thm, ab[0], ab[1]))
            info[nom] = (thm, m, s1, s2)
    return usage, info


def _rapport_fecondite(impls, preuve_de, montre):
    usage, info = fecondite(impls, preuve_de)
    classe = sorted(usage.items(), key=lambda kv: -kv[1])
    print(f"# FÉCONDITÉ — générativité dans le DAG de découverte (≠ MDL/intérêt qui ignorent l'aval) :\n")
    print(f"# top {montre} sources les plus FÉCONDES (nb de découvertes qui les chaînent) :")
    for nom, u in classe[:montre]:
        if nom in info:
            concl = _fmt(info[nom][0].conclusion)
            libel = f"[découverte {nom}] {concl[:90] + '…' if len(concl) > 90 else concl}"
        else:
            libel = f"[corpus] {nom}"
        print(f"#   {u:>4} usages  {libel}")
    n_corpus = sum(1 for n, _ in classe[:montre] if n not in info)
    n_disc = montre - n_corpus
    print(f"\n# Sur le top {montre} : {n_corpus} lemmes-pivots du CORPUS (p.ex. image_croissante, la")
    print(f"# monotonie de l'image qui se re-chaîne partout) et {n_disc} DÉCOUVERTES du système devenues")
    print(f"# elles-mêmes des hubs générateurs. La fécondité (générativité EN AVAL) est un signal")
    print(f"# PROSPECTIF distinct de MDL (fréquence passée) et de l'intérêt (parcimonie/pont) : un")
    print(f"# théorème vu UNE fois peut engendrer un sous-arbre entier → c'est le critère manquant pour")
    print(f"# repérer une notion FÉCONDE (pas juste fréquente ou compacte). Front-ouvert : APPRENDRE à")
    print(f"# le prédire A PRIORI (avant de dépenser les tours) fermerait la boucle de l'invention féconde.")
    return 0
