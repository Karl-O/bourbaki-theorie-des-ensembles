#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tracer une preuve au niveau des primitives N.* = la TRAJECTOIRE pas-à-pas (DAG).

Pas 2 du pivot méta-algo (cf. outils_ia/corpus/README.md). `Theoreme` ne stocke pas
ses prémisses ; pour obtenir la *marche sur le DAG de dérivation* on OBSERVE le noyau
en action : on enveloppe TEMPORAIREMENT les primitives du noyau abrégé pour
JOURNALISER chaque application de règle = (règle, théorèmes-entrée, théorème-sortie).

SOUNDNESS INTACTE — c'est un OBSERVATEUR PUR : le wrapper appelle la VRAIE primitive et
renvoie SA sortie réelle ; il ne fait que la consigner. Il ne peut pas fabriquer ni
altérer un Theoreme (il n'a pas la clé `_CLE` du noyau). Outillage seulement
(`outils_ia/`), restauré dans un `finally` ; JAMAIS dans le code de preuve `bourbaki/`.
(La règle « no monkeypatch » du projet vise le CODE DE PREUVE — interdiction de forger
des théorèmes ; ici on fait l'inverse : on regarde le noyau prouver, sans rien forger.)

Sortie : pour un théorème, une LISTE ORDONNÉE de pas
  { i, rule, inputs:[indices des pas-entrée], concl: AST, clos, n_hyp }
soit la trajectoire complète primitive-par-primitive (le « bruit » de la diffusion =
effacer des pas ; le « débruitage » = les reconstruire ; le noyau filtre chaque pas).
"""
from __future__ import annotations

import functools
import sys
from contextlib import contextmanager
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N  # noqa: E402

PRIMITIVES = ["assume", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "existe_temoin",
              "reflexivite", "alpha_tau", "axiome", "modus_ponens", "loi_deduction",
              "generalisation"]


def _est_thm(x) -> bool:
    return type(x).__name__ == "Theoreme"


class Trace:
    """Accumulateur de pas. `_id2idx` mappe chaque Theoreme produit → l'indice du pas."""

    def __init__(self):
        self.steps: list[dict] = []
        self._id2idx: dict[int, int] = {}

    def record(self, rule: str, args: tuple, kwargs: dict, out) -> None:
        if not _est_thm(out):
            return
        inputs = [self._id2idx[id(x)]
                  for x in (*args, *kwargs.values())
                  if _est_thm(x) and id(x) in self._id2idx]
        idx = len(self.steps)
        if id(out) not in self._id2idx:        # 1ʳᵉ production de ce Theoreme
            self._id2idx[id(out)] = idx
        self.steps.append({
            "i": idx, "rule": rule, "inputs": inputs,
            "concl": repr(out.conclusion), "clos": out.est_clos,
            "n_hyp": len(out.hypotheses),
        })


@contextmanager
def tracer():
    """Contexte qui enveloppe les primitives N.* pour les journaliser, puis restaure."""
    tr = Trace()
    origs = {name: getattr(N, name) for name in PRIMITIVES if hasattr(N, name)}

    def make(name, fn):
        @functools.wraps(fn)
        def wrapper(*a, **k):
            out = fn(*a, **k)                  # VRAIE primitive du noyau
            tr.record(name, a, k, out)
            return out
        return wrapper

    try:
        for name, fn in origs.items():
            setattr(N, name, make(name, fn))   # observateur (outillage), restauré ci-dessous
        yield tr
    finally:
        for name, fn in origs.items():
            setattr(N, name, fn)               # restauration systématique


def tracer_theoreme(fn, *args, **kwargs):
    """Exécute fn(...) en traçant ; renvoie (Theoreme, steps:list[dict]).

    `steps` est la trajectoire primitive-par-primitive ; le dernier pas dont la
    conclusion == celle du théorème est le pas FINAL (racine du DAG)."""
    with tracer() as tr:
        thm = fn(*args, **kwargs)
    return thm, tr.steps


if __name__ == "__main__":
    # démo : tracer un théorème et afficher la trajectoire
    import importlib
    modname = sys.argv[1] if len(sys.argv) > 1 else \
        "bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple"
    fnname = sys.argv[2] if len(sys.argv) > 2 else "couple_diagonale"
    fn = getattr(importlib.import_module(modname), fnname)
    thm, steps = tracer_theoreme(fn)
    print(f"# {fnname} : {len(steps)} pas, clos={thm.est_clos}, n_hyp={len(thm.hypotheses)}")
    for s in steps:
        src = "" if not s["inputs"] else " ←" + ",".join(f"#{j}" for j in s["inputs"])
        print(f"  #{s['i']:>3} {s['rule']:<14}{src}")
