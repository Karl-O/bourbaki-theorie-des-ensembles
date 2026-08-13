#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""UN TOUR COMPLET du système auto-améliorant — le blackboard qui tourne (JALON 4).

Point d'entrée unique qui cadence, en une passe, les deux moitiés du volant, toutes deux
tranchées par le noyau (frontière 22 axiomes intacte) :

  · SLEEP-ABSTRACTION (flywheel.executer) : mine → anti-unifie → promeut en tactique dérivée
    (gate MDL), mesure le COMPOUNDING (portée-CAP + ordre 2), écrit la bibliothèque apprise ;
  · DÉCOUVERTE (conjecturer)               : trouve des problèmes par terme partagé (transitivité
    + détachement) et les RÉSOUT au noyau → nouveaux théorèmes clos, absents du corpus.

Écrit UN enregistrement par tour dans `tour_journal.jsonl` (métriques d'abstraction + découverte)
= la trace de la spirale qui tourne. C'est le geste « cadencer le volant dans /loop » : chaque
appel = un tour de blackboard. Aucune mutation de `bourbaki/` (dry-run/préflight).

Outillage seulement (outils_ia/) ; le noyau reste seul juge.
USAGE : python outils_ia/corpus/tour.py [package…] [--essais N] [--montre K]
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

from flywheel import executer, _journaliser                   # noqa: E402
from conjecturer import (_corpus, conjecturer, _fmt, _interet,  # noqa: E402
                         iterer_egalites, equivalences_de, chainer_equivalences,
                         pool_inclusions, chainer_inclusions, chainer_existentiels, _profond)
from promo_notion import PACKAGES                              # noqa: E402

_JOURNAL = _ICI / "tour_journal.jsonl"


def main(argv):
    rest = argv[1:]
    essais = int(rest[rest.index("--essais") + 1]) if "--essais" in rest else 155
    montre = int(rest[rest.index("--montre") + 1]) if "--montre" in rest else 6
    packages = [a for a in rest if not a.startswith("--") and not a.isdigit()] or PACKAGES

    print("# ══ TOUR COMPLET du volant auto-améliorant ══", file=sys.stderr)

    # ── moitié 1 : abstraction (invente des notions par compression) ────────────
    rec, acceptes = executer(packages, essais)

    # ── moitié 2 : découverte (trouve des problèmes & les résout) ───────────────
    print(f"\n# (4) DÉCOUVERTE — problèmes trouvés par terme partagé & résolus au noyau :")
    impls, preuve_de = _corpus(packages)
    trouves = conjecturer(impls, preuve_de)
    n_det = sum(1 for t in trouves if t[0].startswith("détach"))
    n_tr = sum(1 for t in trouves if t[0].startswith("transit"))
    print(f"#  {len(preuve_de)} théorèmes clos, {len(impls)} implications → {len(trouves)} NOUVEAUX "
          f"théorèmes certifiés ({n_det} détach., {n_tr} transit.)")
    for (mode, s1, s2, thm) in trouves[:montre]:
        concl = _fmt(thm.conclusion)
        if len(concl) > 140:
            concl = concl[:137] + "…"
        print(f"#     [{mode}] {concl}")

    # ── moitié 3 (RELIE) : algèbre — égalités itérées + équivalences ───────────
    print(f"\n# (5) ALGÈBRE — chaînage des égalités (itéré, compounding) + équivalences :")
    egal_tous, egal_tours = iterer_egalites(preuve_de, rounds=3)
    prof2 = sum(1 for (_, s1, s2, _) in egal_tous if _profond(s1, s2))
    par_t = " / ".join(str(len(d)) for d in egal_tours)
    print(f"#  égalités : {len(egal_tous)} identités nouvelles sur 3 tours ({par_t}), "
          f"dont {prof2} de profondeur ≥2")
    eqv = chainer_equivalences(equivalences_de(preuve_de), preuve_de)
    print(f"#  équivalences : {len(eqv)} caractérisations nouvelles")
    incls, n_ic, n_pont = pool_inclusions(preuve_de, egal_tous)
    incl_tous = chainer_inclusions(incls, preuve_de)
    n_via_pont = sum(1 for (_, s1, s2, _) in incl_tous
                     if s1.startswith("pont:") or s2.startswith("pont:"))
    print(f"#  inclusions : {len(incl_tous)} nouvelles ({n_ic} ⊂-corpus + {n_pont} pont =→⊂ ; "
          f"{n_via_pont} découvertes via le pont)")
    exi = chainer_existentiels(preuve_de)
    print(f"#  existentiels : {len(exi)} théorèmes ∃ nouveaux (∃-intro S5, sous-termes récurrents)")
    for (mode, s1, s2, thm) in sorted(egal_tous + eqv + incl_tous,
                                      key=lambda t: _interet(*t), reverse=True)[:3]:
        st = _fmt(thm.conclusion)
        print(f"#     [{mode}] {st[:130] + '…' if len(st) > 130 else st}")

    # ── journal unifié du tour ──────────────────────────────────────────────────
    rec = {**rec, "n_implications": len(impls), "n_conjectures": len(trouves),
           "conj_detach": n_det, "conj_transit": n_tr,
           "n_egalites": len(egal_tous), "egal_prof2": prof2, "n_equivalences": len(eqv),
           "n_inclusions": len(incl_tous), "incl_via_pont": n_via_pont,
           "n_existentiels": len(exi)}
    tour = _journaliser(_JOURNAL, rec)

    total = len(trouves) + len(egal_tous) + len(eqv) + len(incl_tous) + len(exi)
    print(f"\n# ══ TOUR #{tour} bouclé ══  {rec['n_promues']} notions promues (gain MDL "
          f"≈{rec['gain_mdl']}), {rec['ordre2']} macros d'ordre 2, {total} découvertes "
          f"({len(trouves)} ⇒ + {len(egal_tous)} = + {len(eqv)} ⇔ + {len(incl_tous)} ⊂ "
          f"+ {len(exi)} ∃).")
    print(f"# journal → {_JOURNAL.name} ; bibliothèque → notions_apprises.py")
    print("# = le volant a tourné sur les 5 régimes (⇒, =, ⇔, ⊂, ∃) reliés par le pont S6, "
          "noyau juge, 22 axiomes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
