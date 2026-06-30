#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Analyse stats du corpus pour CALIBRER le générateur (pivot méta-algo, pas 4).

Lit un JSONL produit par export_corpus.py et calcule ce dont a besoin la conception
d'un générateur generate-and-verify (GFlowNet/diffusion sur le DAG) :

  1. DISTRIBUTION des trajectoires (`trace_len`) = échelle de la « marche » à apprendre
     (min/médiane/max/total des pas primitifs) — fixe le budget T de diffusion.
  2. VOCABULAIRE de règles (`rule_hist` agrégé) = l'espace d'ACTIONS primitif du noyau.
  3. RÉUTILISATION de lemmes/tactiques : on parse `proof_src` pour les appels de
     fonctions (helpers/tactiques/lemmes) → la BIBLIOTHÈQUE de fait (les briques que le
     générateur doit connaître ; pertinent pour le volet library-learning).
  4. Répartition par chapitre (via @livre) + ratio clos/conditionnel.

USAGE : python outils_ia/corpus/stats_corpus.py [corpus.jsonl]   (défaut corpus_sample.jsonl)
"""
from __future__ import annotations

import collections
import json
import re
import statistics
import sys
from pathlib import Path

_ICI = Path(__file__).resolve().parent
_DEFAUT = _ICI / "corpus_sample.jsonl"
# appel de fonction nommée : \b nom ( …  (on filtre le bruit après)
_CALL = re.compile(r"\b([a-z_][a-z0-9_]{2,})\s*\(")
_BRUIT = {"len", "range", "set", "sorted", "list", "dict", "str", "repr", "int",
          "isinstance", "getattr", "var", "print", "frozenset", "tuple", "enumerate"}


def main(argv: list[str]) -> int:
    chemin = Path(argv[1]) if len(argv) > 1 else _DEFAUT
    recs = [json.loads(l) for l in open(chemin, encoding="utf-8")]
    n = len(recs)
    print(f"# corpus : {chemin.name} — {n} théorèmes")
    print(f"clos {sum(r['clos'] for r in recs)} | conditionnels {sum(not r['clos'] for r in recs)}"
          f" | verified {sum(r['verified'] is True for r in recs)} | @livre {sum(bool(r['livre']) for r in recs)}")

    # 1. trajectoires
    lens = [r["trace_len"] for r in recs if r.get("trace_len")]
    if lens:
        print(f"\n[1] TRAJECTOIRES (pas primitifs) : n={len(lens)} tracés ; "
              f"min {min(lens)} | médiane {int(statistics.median(lens))} | max {max(lens)} | total {sum(lens)}")

    # 2. vocabulaire de règles (espace d'actions)
    rules = collections.Counter()
    for r in recs:
        for k, v in (r.get("rule_hist") or {}).items():
            rules[k] += v
    if rules:
        tot = sum(rules.values())
        print(f"\n[2] VOCABULAIRE DE RÈGLES ({tot} applications) :")
        for rule, c in rules.most_common():
            print(f"    {rule:<16} {c:>8}  ({100*c/tot:4.1f}%)")

    # 3. réutilisation de lemmes/tactiques (bibliothèque de fait)
    biblio = collections.Counter()
    for r in recs:
        src = r.get("proof_src") or ""
        for nom in set(_CALL.findall(src)):
            if nom not in _BRUIT and nom != r["name"]:
                biblio[nom] += 1
    if biblio:
        print(f"\n[3] BIBLIOTHÈQUE — briques les plus réutilisées (nb de preuves qui l'appellent) :")
        for nom, c in biblio.most_common(20):
            print(f"    {nom:<28} {c:>4}")

    # 4. par chapitre
    ch = collections.Counter()
    for r in recs:
        if r["livre"]:
            m = re.search(r"Ch\.(\w+)", r["livre"])
            if m:
                ch[m.group(1)] += 1
    if ch:
        print(f"\n[4] PAR CHAPITRE : {dict(ch.most_common())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
