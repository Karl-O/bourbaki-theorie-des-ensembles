#!/usr/bin/env python3
"""Mirroring des tests sur l'arborescence de ``bourbaki/`` (cf. CLAUDE.md : tests/ calque bourbaki/).

Après la migration de ``bourbaki/`` (outils_ia/migration_arbre.py), les fichiers
``tests/<pkg>/test_*.py`` sont restés À PLAT. Ce script les range dans le sous-dossier
**miroir** de leur module : pour chaque test, on lit les imports ``bourbaki.<pkg>...``,
on **résout le module sur le disque** (plus long préfixe pointé qui est un .py existant),
et on prend le sous-dossier (relatif à ``bourbaki/<pkg>``) du module dont le nom colle le
mieux au nom du test (``test_FOO`` ↔ ``…_FOO``). Le test va dans
``tests/<pkg>/<ce_sous_dossier>/test_FOO.py``.

SÛRETÉ — TRANSACTIONNEL : préflight (arbre propre, sources présentes, destinations libres)
puis apply protégé avec ROLLBACK auto (git reset --hard + git clean). Jamais d'état partiel.

Usage (depuis V9/) ::

    python outils_ia/mirror_tests.py cardinaux            # dry-run
    python outils_ia/mirror_tests.py cardinaux --apply
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path.cwd()


def _git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)


def _resolve_module(parts):
    """parts = ['cardinaux','iii_3','cantor_bernstein','ensembles_cantor_bernstein','func']
    → renvoie les parts du MODULE (plus long préfixe formant un .py existant), ou None."""
    for k in range(len(parts), 0, -1):
        if (ROOT / "bourbaki" / ("/".join(parts[:k]) + ".py")).exists():
            return parts[:k]
    return None


def _strip(name):
    return name.removeprefix("ensembles_").removeprefix("test_")


def _target_subdir(testfile: Path, pkg: str):
    """Sous-dossier cible (relatif à tests/<pkg>) pour ce test, ou None si indéterminable."""
    text = testfile.read_text(encoding="utf-8")
    key = _strip(testfile.stem)  # nom du test sans 'test_'
    # tous les chemins pointés bourbaki.<pkg>.… référencés
    raw = []  # listes de parts candidates (commençant par <pkg>)
    # forme contiguë : bourbaki.<pkg>.a.b.c  (import a.b.c / a.b.c.attr / from a.b.c import func)
    for m in re.findall(r"bourbaki\.(" + re.escape(pkg) + r"(?:\.[A-Za-z0-9_]+)+)", text):
        raw.append(m.split("."))
    # forme 'from bourbaki.<pkg>[.a.b] import NAME' : le MODULE est parent + NAME
    for par, nm in re.findall(
            r"from\s+bourbaki\.(" + re.escape(pkg) + r"(?:\.[A-Za-z0-9_]+)*)\s+import\s+\(?\s*([A-Za-z0-9_]+)", text):
        raw.append(par.split(".") + [nm])
    cands = []  # (subdir_rel, module_leaf)
    for parts in raw:
        mod = _resolve_module(parts)
        if mod and len(mod) >= 2:           # au moins pkg + module
            cands.append(("/".join(mod[1:-1]), mod[-1]))
    if not cands:
        return None
    # meilleur = nom de module le plus proche du nom du test
    def score(leaf):
        s = _strip(leaf)
        if s == key:
            return 3
        if s in key or key in s:
            return 2
        return 0
    cands.sort(key=lambda c: -score(c[1]))
    best_sub, best_leaf = cands[0]
    if score(best_leaf) == 0:
        # aucun match de nom : on prend le sous-dossier le plus fréquent
        from collections import Counter
        best_sub = Counter(c[0] for c in cands).most_common(1)[0][0]
    return best_sub


def main() -> int:
    ap = argparse.ArgumentParser(description="Mirroring transactionnel des tests sur bourbaki/.")
    ap.add_argument("pkg", help="paquet, ex: cardinaux")
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    dry = not args.apply
    root = ROOT / "tests" / args.pkg
    if not root.is_dir():
        sys.exit(f"introuvable: tests/{args.pkg}")

    moves, unmatched = [], []
    for f in sorted(root.rglob("test_*.py")):
        sub = _target_subdir(f, args.pkg)
        cur_rel = f.relative_to(root).as_posix()
        if sub is None:
            unmatched.append(cur_rel)
            continue
        dst = f"tests/{args.pkg}/{sub}/{f.name}"
        if Path(dst) != f.relative_to(ROOT):
            moves.append((f.relative_to(ROOT).as_posix(), dst))

    print(f"[{'DRY-RUN' if dry else 'APPLY'}] tests/{args.pkg} : {len(moves)} déplacements, "
          f"{len(unmatched)} sans cible")
    for de, ve in moves[:12]:
        print(f"      {de}  ->  {ve}")
    if len(moves) > 12:
        print(f"      ... (+{len(moves) - 12})")
    if unmatched:
        print("  sans cible (laissés en place) :", unmatched[:10])

    if dry:
        return 0

    # préflight
    errs = []
    if _git("status", "--porcelain").stdout.strip():
        errs.append("arbre git NON PROPRE — commit/stash d'abord.")
    for de, ve in moves:
        if not (ROOT / de).exists():
            errs.append(f"source absente : {de}")
        if (ROOT / ve).exists():
            errs.append(f"destination déjà présente : {ve}")
    if errs:
        print("  PRÉFLIGHT ÉCHOUÉ — aucun changement :")
        for e in errs:
            print("   -", e)
        return 1

    try:
        for de, ve in moves:
            (ROOT / ve).parent.mkdir(parents=True, exist_ok=True)
            r = _git("mv", de, ve)
            if r.returncode != 0:
                raise RuntimeError(f"git mv {de} -> {ve} : {r.stderr.strip()}")
        # __init__.py dans chaque nouveau dossier de tests
        for d in {os.path.dirname(ve) for _, ve in moves}:
            ini = ROOT / d / "__init__.py"
            if not ini.exists():
                ini.write_text("", encoding="utf-8")
    except Exception as exc:  # noqa: BLE001
        print(f"  ERREUR : {exc}\n  -> ROLLBACK auto...")
        _git("reset", "--hard", "HEAD")
        _git("clean", "-fd", f"tests/{args.pkg}")
        print("  dépôt restauré.")
        return 1

    print(f"  OK : {len(moves)} tests déplacés.  -> pytest --co ; commit")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
