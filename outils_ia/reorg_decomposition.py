#!/usr/bin/env python3
"""Réécrit les imports après déplacement des modules decomposition_* vers
ii_6_5_decomposition/ (motif A dotté + motif B `from PARENT import NAME`).

À lancer UNE fois sur un arbre propre (après les git mv).
"""
import sys
import pathlib

V9 = pathlib.Path(sys.argv[1])
OLD = "bourbaki.ensembles.ii_6_equivalence"
SUB = "bourbaki.ensembles.ii_6_equivalence.ii_6_5_decomposition"
MODS = ["ensembles_decomposition_effective", "ensembles_decomposition_quotient"]

repls = []
for m in MODS:
    repls.append((f"{OLD}.{m}", f"{SUB}.{m}"))          # motif A : chemin dotté
    repls.append((f"{OLD} import {m}", f"{SUB} import {m}"))  # motif B : from PARENT import NAME

SKIP = {"__pycache__", ".git", ".venv", ".pytest_cache", ".claude", "node_modules"}
n_files = 0
for p in V9.rglob("*.py"):
    if any(part in SKIP for part in p.parts):
        continue
    txt = p.read_text(encoding="utf-8")
    new = txt
    for a, b in repls:
        new = new.replace(a, b)
    if new != txt:
        p.write_text(new, encoding="utf-8")
        n_files += 1
        print("reecrit:", p.relative_to(V9))
print(f"total fichiers reecrits: {n_files}")
