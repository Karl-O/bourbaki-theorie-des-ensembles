#!/usr/bin/env python3
"""Profilage d'un théorème lourd pour trouver le hotspot du noyau (ÉTAPE D).

Usage : python outils_ia/profil_hotspot.py  (depuis V9/) — profile trois_impair
(le proof cardinal non-récursif ~400s) et écrit le top des fonctions dans
outils_ia/profil_hotspot.txt (par tottime ET cumulative).
"""
import cProfile
import importlib
import io
import os
import pstats
import sys
from pathlib import Path

sys.path.insert(0, os.getcwd())  # V9/ (cwd) pour importer bourbaki hors pytest

MOD = "bourbaki.cardinaux.iii_6_infinis.denombrable.ensembles_denombrable_injection_iii6"
FN = "trois_impair"

m = importlib.import_module(MOD)
fn = getattr(m, FN)

pr = cProfile.Profile()
pr.enable()
res = fn()
pr.disable()

s = io.StringIO()
s.write(f"=== {MOD}.{FN}  est_clos={res.est_clos} ===\n\n")
ps = pstats.Stats(pr, stream=s)
s.write("---- par tottime (temps propre, hors sous-appels) ----\n")
ps.sort_stats("tottime").print_stats(30)
s.write("\n---- par cumulative (temps total avec sous-appels) ----\n")
ps.sort_stats("cumulative").print_stats(25)
Path("outils_ia/profil_hotspot.txt").write_text(s.getvalue(), encoding="utf-8")
print("profil écrit dans outils_ia/profil_hotspot.txt")
