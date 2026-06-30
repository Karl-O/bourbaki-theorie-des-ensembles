#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Courbe de SENSIBILITÉ AU BUDGET (CAP) du taux end-to-end (pas 36).

Le 27 % de pas 33 est mesuré à CAP=200. Ici on quantifie comment le taux end-to-end MONTE avec le
budget d'essais-noyau, SANS plus de données : un seul run leave-one-module-out à CAP_MAX, où
`regen_e2e` renvoie l'INDICE n du 1er succès noyau (≤ CAP_MAX) ; pour chaque CAP testé, un bloc compte
comme régénéré si n ≤ CAP. Donne la courbe BRUT vs TreeNN d'un coup. Mesure la PORTÉE pratique du
ranker structuré (combien de blocs deviennent atteignables si on dépense plus d'essais-noyau).

Réutilise proto_synth_e2e (regen kernel-validé instrumenté) + proto_synth_torch. Outillage seulement.
USAGE : python outils_ia/corpus/proto_synth_capcurve.py
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

import proto_synth_e2e as E2E                                  # noqa: E402
from proto_synth_torch import collecte_slots, _entraine, MODULES  # noqa: E402
from proto_macro_noyau import _proofs, TEST_LOURD             # noqa: E402

CAP_MAX = 400            # budget max exploré (borne le temps kernel ; courbe jusqu'à 400)
E_LOMO = 1
CAPS = [50, 100, 200, 300, 400]


def main(argv):
    E2E.CAP = CAP_MAX
    print(f"# courbe CAP-sensibilité : leave-one-module-out à CAP_MAX={CAP_MAX} (E={E_LOMO})…",
          file=sys.stderr)
    tot = {"blocs": 0, "in_gram": 0, "brut": 0, "tree": 0}
    for held in MODULES:
        train_mods = [m for m in MODULES if m != held]
        nets = [_entraine(collecte_slots(train_mods), seed=sd) for sd in range(E_LOMO)]
        court = held.split(".")[-1]
        print(f"# [{court}] entraîné ; régénération…", file=sys.stderr)
        _, proofs = _proofs(held)
        for P in proofs:
            if P in TEST_LOURD:
                continue
            E2E._eval_proof(held, P, nets, tot)

    brut_ns = tot.get("brut_ns", [])
    tree_ns = tot.get("tree_ns", [])
    n_blocs = len(tree_ns)
    print(f"\n# pas 36 — COURBE CAP-SENSIBILITÉ end-to-end ({n_blocs} blocs in-gram, leave-one-module-out) :")
    print(f"#  {'CAP':>5} | {'BRUT':>6} | {'TreeNN':>7}")
    rows = []
    for cap in CAPS:
        b = sum(1 for n in brut_ns if n is not None and n <= cap)
        t = sum(1 for n in tree_ns if n is not None and n <= cap)
        rows.append((cap, b, t))
        print(f"#  {cap:>5} | {100*b//n_blocs:>5}% | {100*t//n_blocs:>6}%")
    if n_blocs and rows:
        t200 = next((t for c, b, t in rows if c == 200), 0)
        tmax = rows[-1][2]
        print(f"# → TreeNN end-to-end : {100*t200//n_blocs}% @CAP=200 → {100*tmax//n_blocs}% @CAP={CAPS[-1]} "
              f"(sur {n_blocs} blocs). Plus de budget atteint plus de blocs SANS plus de données.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
