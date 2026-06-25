#!/usr/bin/env python3
"""Migration d'arborescence ≤10/dossier (cf. CLAUDE.md, REORG_PLAN.md).

Déplace les fichiers d'UN paquet selon ``outils_ia/reorg_moves.json`` (``git mv``),
crée les ``__init__.py`` manquants, et réécrit les imports absolus impactés dans
``bourbaki/`` ET ``tests/``.

Réécriture d'import (frontières strictes — ne corrompt jamais un préfixe de module) :
  * motif A : chemin pointé contigu  ``a.b.c`` -> ``a.b.sub.c``
    (couvre ``import a.b.c``, ``a.b.c.attr``, ``from a.b.c import (noms)``)
  * motif B : ``from PARENT import NAME [as ALIAS]`` -> ``from NEWPARENT import NAME``
    (NAME = sous-module déplacé ; la forme dominante du dépôt)

SÛRETÉ — TRANSACTIONNEL (jamais d'état partiel cassé) :
  1. **Préflight** AVANT toute mutation : arbre git propre (sinon un rollback effacerait
     du travail non commité), chaque source présente, chaque destination libre. Échec ⇒
     AUCUN changement.
  2. **Apply protégé** : la moindre exception (ex. ``git mv`` qui échoue) déclenche un
     **ROLLBACK automatique** (``git reset --hard`` + ``git clean -fd <paquet>``) ⇒ le
     dépôt revient EXACTEMENT à l'état d'avant.

Usage (depuis V9/) ::

    python outils_ia/migration_arbre.py bourbaki/logique            # dry-run
    python outils_ia/migration_arbre.py bourbaki/logique --apply
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path.cwd()
MOVES_JSON = ROOT / "outils_ia" / "reorg" / "reorg_moves.json"


def _dotted(path: str):
    return path[:-3].replace("/", ".") if path.endswith(".py") else None


_EXCLUDE = {"__pycache__", ".git", ".pytest_cache", ".venv", ".claude", "node_modules"}


def _all_py():
    """TOUS les .py de V9 (bourbaki/, tests/, outils_ia/, .py racine…), hors dossiers
    techniques. IMPORTANT : ne pas se limiter à bourbaki/+tests/ — outils_ia/ et les
    scripts racine importent aussi des modules bourbaki et doivent être réécrits."""
    for f in ROOT.rglob("*.py"):
        if not any(part in _EXCLUDE for part in f.parts):
            yield f


def _git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)


def _preflight(moves):
    """Erreurs bloquantes (liste vide = OK). Garantit qu'un rollback est sûr et que
    rien ne va écraser un fichier existant."""
    errs = []
    if _git("status", "--porcelain").stdout.strip():
        errs.append("arbre git NON PROPRE — commit/stash d'abord (un rollback en cas "
                    "d'échec effacerait ces changements non commités).")
    for de, vers in moves:
        if not (ROOT / de).exists():
            errs.append(f"source absente : {de}")
        if (ROOT / vers).exists():
            errs.append(f"destination déjà présente : {vers}")
    return errs


def _build_patterns(moves, pkg_renames=()):
    """(rmap, fmap, pats) — cartes + motifs de réécriture compilés.

    ``pkg_renames`` = déplacements de PAQUETS (dossiers entiers). On ajoute le chemin
    pointé du paquet lui-même à rmap (motif A) — indispensable pour réécrire
    ``from PKG import nom_reexporté`` / ``import PKG`` / ``PKG.attr`` quand un sous-paquet
    bouge (ses noms ré-exportés par __init__ ne sont sinon pas suivis)."""
    rmap, fmap = {}, {}
    for de, vers in moves:
        if de.endswith("__init__.py"):
            continue
        od, nd = _dotted(de), _dotted(vers)
        if od and nd and od != nd:
            rmap[od] = nd
            op, name = od.rsplit(".", 1)
            np_, _ = nd.rsplit(".", 1)
            fmap[(op, name)] = np_
    for r in pkg_renames:
        od = r["de"].rstrip("/").replace("/", ".")
        nd = r["vers"].rstrip("/").replace("/", ".")
        if od != nd:
            rmap[od] = nd
    pats = [(re.compile(r"(?<![\w.])" + re.escape(o) + r"(?![\w])"), n)
            for o, n in sorted(rmap.items(), key=lambda kv: -len(kv[0]))]
    #   `\(?\s*` après `import` : couvre aussi la forme parenthésée mono-sous-module
    #   `from PKG import (\n    NAME as X)`. (Multi-sous-modules parenthésés : absents du dépôt.)
    pats += [(re.compile(r"(?m)^(\s*from\s+)" + re.escape(op) + r"(\s+import\s+\(?\s*)"
                         + re.escape(name) + r"(?![\w])"), r"\1" + np_ + r"\2" + name)
             for (op, name), np_ in fmap.items()]
    return rmap, fmap, pats


def main() -> int:
    ap = argparse.ArgumentParser(description="Migration d'arborescence par paquet (transactionnel).")
    ap.add_argument("paquet", help="ex: bourbaki/logique")
    ap.add_argument("--apply", action="store_true", help="exécute (sinon dry-run)")
    args = ap.parse_args()
    dry = not args.apply

    data = json.loads(MOVES_JSON.read_text(encoding="utf-8"))
    if args.paquet not in data:
        sys.exit(f"paquet inconnu: {args.paquet}\n  disponibles: {list(data)}")
    moves = [(m["de"], m["vers"]) for m in data[args.paquet]["deplacements"] if m["de"] != m["vers"]]

    # validation de FORMAT (évite tout crash plus loin) : chemins V9-root-relatifs (bourbaki/…)
    # désignant des fichiers (un parent + un nom). Échec ⇒ erreur claire, aucune mutation.
    bad = [f"{de} -> {ve}" for de, ve in moves
           if not (de.startswith("bourbaki/") and "/" in de.rstrip("/")
                   and ve.startswith("bourbaki/") and "/" in ve.rstrip("/")
                   and de.endswith(".py") and ve.endswith(".py"))]
    if bad:
        sys.exit("move-map MALFORMÉ (corriger outils_ia/reorg_moves.json) :\n  " + "\n  ".join(bad[:10]))

    pkg_renames = data[args.paquet].get("renommages_paquets", [])
    rmap, fmap, pats = _build_patterns(moves, pkg_renames)
    new_dirs = {d for d in (os.path.dirname(v) for _, v in moves) if d}

    rel = []
    for de, _v in moves:
        if (ROOT / de).exists():
            for i, line in enumerate((ROOT / de).read_text(encoding="utf-8").splitlines(), 1):
                if re.match(r"\s*from\s+\.", line):
                    rel.append(f"{de}:{i}: {line.strip()}")

    print(f"[{'DRY-RUN' if dry else 'APPLY'}] {args.paquet} : {len(moves)} déplacements, "
          f"{len(rmap)} modules renommés, {len(new_dirs)} dossiers")
    if rel:
        print(f"  /!\\ {len(rel)} import(s) RELATIF(s) — non couverts, à vérifier :")
        for r in rel[:30]:
            print("      ", r)

    if dry:
        for de, vers in moves[:8]:
            print(f"      git mv {de} -> {vers}")
        if len(moves) > 8:
            print(f"      ... (+{len(moves) - 8})")
        n = sum(1 for f in _all_py()
                if any(p.search(f.read_text(encoding="utf-8")) for p, _ in pats))
        print(f"  imports à réécrire dans ~{n} fichier(s) (simulé)")
        return 0

    # ---------- APPLY : préflight, puis transaction avec rollback ----------
    errs = _preflight(moves)
    if errs:
        print("  PRÉFLIGHT ÉCHOUÉ — aucun changement :")
        for e in errs:
            print("   -", e)
        return 1
    try:
        # 1. dossiers (sans __init__ : un move peut amener un __init__ existant)
        for d in sorted(new_dirs):
            (ROOT / d).mkdir(parents=True, exist_ok=True)
        # 2. git mv (échec ⇒ exception ⇒ rollback)
        for de, vers in moves:
            (ROOT / vers).parent.mkdir(parents=True, exist_ok=True)
            r = _git("mv", de, vers)
            if r.returncode != 0:
                raise RuntimeError(f"git mv {de} -> {vers} : {r.stderr.strip()}")
        # 3. __init__.py manquants (après les moves)
        for d in sorted(new_dirs):
            ini = ROOT / d / "__init__.py"
            if not ini.exists():
                ini.write_text("", encoding="utf-8")
        # 4. réécriture des imports
        changed = 0
        for f in _all_py():
            txt = f.read_text(encoding="utf-8")
            new = txt
            for pat, n in pats:
                new = pat.sub(n, new)
            if new != txt:
                f.write_text(new, encoding="utf-8")
                changed += 1
    except Exception as exc:  # noqa: BLE001 — on veut TOUT rattraper pour rollback
        print(f"  ERREUR : {exc}\n  -> ROLLBACK automatique (git reset --hard + clean {args.paquet})...")
        _git("reset", "--hard", "HEAD")
        _git("clean", "-fd", args.paquet)
        print("  dépôt RESTAURÉ à l'état d'avant — aucun changement conservé.")
        return 1

    print(f"  OK : {changed} fichier(s) d'imports réécrits.  -> pytest --co ; commit")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
