#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Régénération END-TO-END en LEAVE-ONE-MODULE-OUT (consolidation, pas 33).

Le 50 % de pas 27 repose sur 2 blocs MIROIR d'identite seulement — non représentatif. Ici on mesure
le taux end-to-end CORPUS-WIDE : pour CHAQUE module, on entraîne le TreeNN sur les 5 AUTRES (holdout
module complet) et on régénère SES blocs in-grammaire (≤2 slots), NOYAU validant, à budget fixe CAP.
On agrège BRUT vs TreeNN sur tout le corpus + détail par module. Les modules NON-miroir devraient
régénérer plus haut que 50 % (pas d'effet miroir adversarial).

Réutilise proto_synth_e2e._eval_proof (regen kernel-validé) + proto_synth_torch (TreeNN). Outillage
seulement (outils_ia/) ; aucun Theoreme forgé. USAGE : python outils_ia/corpus/proto_synth_lomo.py
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

E_LOMO = 1               # 1 graine (vs 2) pour borner le temps (6 entraînements)


def main(argv):
    print(f"# LEAVE-ONE-MODULE-OUT end-to-end sur {len(MODULES)} modules (E={E_LOMO}, CAP={E2E.CAP})…",
          file=sys.stderr)
    tot = {"blocs": 0, "in_gram": 0, "brut": 0, "tree": 0}
    detail = []
    for held in MODULES:
        train_mods = [m for m in MODULES if m != held]
        nets = [_entraine(collecte_slots(train_mods), seed=sd) for sd in range(E_LOMO)]
        court = held.split(".")[-1]
        print(f"# [{court}] entraîné sur {len(train_mods)} modules ; régénération de ses blocs…",
              file=sys.stderr)
        before = dict(tot)
        _, proofs = _proofs(held)
        for P in proofs:
            if P in TEST_LOURD:
                continue
            E2E._eval_proof(held, P, nets, tot)
        dg = tot["in_gram"] - before["in_gram"]
        dt = tot["tree"] - before["tree"]
        db = tot["brut"] - before["brut"]
        detail.append((court, dg, db, dt))
        print(f"# [{court}] {dg} blocs in-gram : BRUT {db} | TreeNN {dt}", file=sys.stderr)

    print("\n# pas 33 — END-TO-END LEAVE-ONE-MODULE-OUT (kernel validant, CAP={}) :".format(E2E.CAP))
    for court, dg, db, dt in detail:
        if dg:
            print(f"#   {court:<42} {dg:>2} blocs : BRUT {db} ({100*db//dg:>3}%) → TreeNN {dt} ({100*dt//dg:>3}%)")
        else:
            print(f"#   {court:<42}  0 bloc in-gram (≤2 slots)")
    ig = tot["in_gram"]
    if ig:
        print(f"# TOTAL corpus : {ig} blocs in-gram → BRUT {tot['brut']} ({100*tot['brut']//ig}%) "
              f"→ TreeNN {tot['tree']} ({100*tot['tree']//ig}%).")
        print(f"# HEADLINE ROBUSTE : {100*tot['tree']//ig}% end-to-end sur {ig} blocs across corpus "
              f"(vs {100*tot['brut']//ig}% brut) — au lieu de « 50% sur 2 blocs miroir » (pas 27).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
