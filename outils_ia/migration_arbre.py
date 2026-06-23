#!/usr/bin/env python3
"""Migration d'arborescence ≤10/dossier (cf. CLAUDE.md, REORG_PLAN.md).

Déplace les fichiers d'UN paquet selon ``outils_ia/reorg_moves.json`` (``git mv``),
crée les ``__init__.py`` des nouveaux sous-dossiers + les dossiers-trous, et réécrit
les imports absolus impactés dans ``bourbaki/`` ET ``tests/``.

La réécriture d'import est la seule partie délicate : on remplace le chemin pointé
``old.dotted`` par ``new.dotted`` avec des frontières strictes
``(?<![\\w.]) old (?![\\w])`` — ainsi ``bourbaki.x.foo`` n'altère JAMAIS
``bourbaki.x.foo_bar`` (préfixe), et ``bourbaki.x.foo.attr`` reste correct.
Les modules sont traités du plus long au plus court par prudence.

Usage (depuis V9/) ::

    python outils_ia/migration_arbre.py bourbaki/structures              # dry-run
    python outils_ia/migration_arbre.py bourbaki/structures --apply      # exécute

Garde-fou : ne touche QU'aux chemins d'import ; la logique des preuves et la
frontière de confiance du noyau sont inchangées.
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
MOVES_JSON = ROOT / "outils_ia" / "reorg_moves.json"


def _dotted(path: str) -> str | None:
    """``"bourbaki/structures/x.py"`` -> ``"bourbaki.structures.x"`` (None si non .py)."""
    return path[:-3].replace("/", ".") if path.endswith(".py") else None


def _all_py():
    """Tous les .py de bourbaki/ et tests/, hors __pycache__."""
    for base in ("bourbaki", "tests"):
        root = ROOT / base
        if not root.exists():
            continue
        for f in root.rglob("*.py"):
            if "__pycache__" not in f.parts:
                yield f


def main() -> int:
    ap = argparse.ArgumentParser(description="Migration d'arborescence par paquet.")
    ap.add_argument("paquet", help="ex: bourbaki/structures")
    ap.add_argument("--apply", action="store_true", help="exécute (sinon dry-run)")
    args = ap.parse_args()
    dry = not args.apply

    data = json.loads(MOVES_JSON.read_text(encoding="utf-8"))
    if args.paquet not in data:
        sys.exit(f"paquet inconnu: {args.paquet}\n  disponibles: {list(data)}")
    pk = data[args.paquet]
    moves = [(m["de"], m["vers"]) for m in pk["deplacements"] if m["de"] != m["vers"]]

    # 1) carte de réécriture old.dotted -> new.dotted (fichiers .py, hors __init__)
    rmap: dict[str, str] = {}              # old.dotted -> new.dotted  (motif A : chemin contigu)
    fmap: dict[tuple[str, str], str] = {}  # (old_parent, name) -> new_parent  (motif B : from import)
    for de, vers in moves:
        if de.endswith("__init__.py"):
            continue
        od, nd = _dotted(de), _dotted(vers)
        if od and nd and od != nd:
            rmap[od] = nd
            op, name = od.rsplit(".", 1)
            np_, _ = nd.rsplit(".", 1)
            fmap[(op, name)] = np_

    # 2) détection d'imports RELATIFS dans le paquet (non couverts par la réécriture)
    rel = []
    for de, _ in moves:
        fp = ROOT / de
        if fp.exists():
            for i, line in enumerate(fp.read_text(encoding="utf-8").splitlines(), 1):
                if re.match(r"\s*from\s+\.", line):
                    rel.append(f"{de}:{i}: {line.strip()}")

    mode = "DRY-RUN" if dry else "APPLY"
    print(f"[{mode}] {args.paquet} : {len(moves)} déplacements, {len(rmap)} modules renommés")
    if rel:
        print(f"  /!\\ {len(rel)} import(s) RELATIF(s) détecté(s) — à corriger à la main :")
        for r in rel[:30]:
            print("      ", r)

    # 3) dossiers à créer (parents des cibles + dossiers-trous)
    new_dirs = {os.path.dirname(vers) for _, vers in moves}
    new_dirs |= {d["dossier"].rstrip("/") for d in pk.get("dossiers_vides", [])}
    new_dirs = {d for d in new_dirs if d}

    if dry:
        print(f"  dossiers à créer ({len(new_dirs)}) : {sorted(new_dirs)}")
        for de, vers in moves[:8]:
            print(f"      git mv {de} -> {vers}")
        if len(moves) > 8:
            print(f"      ... (+{len(moves) - 8} autres)")
    else:
        for d in sorted(new_dirs):
            (ROOT / d).mkdir(parents=True, exist_ok=True)
            ini = ROOT / d / "__init__.py"
            if not ini.exists():
                ini.write_text("", encoding="utf-8")
        for de, vers in moves:
            (ROOT / vers).parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "mv", de, vers], cwd=ROOT, check=True)

    # 4) réécriture des imports dans tout bourbaki/ + tests/
    #   motif A — chemin pointé contigu  bourbaki.x.foo -> bourbaki.x.sub.foo
    #             (couvre `import a.b.c`, `a.b.c.attr`, `from a.b.c import (noms)`)
    pats_a = [
        (re.compile(r"(?<![\w.])" + re.escape(o) + r"(?![\w])"), n)
        for o, n in sorted(rmap.items(), key=lambda kv: -len(kv[0]))
    ]
    #   motif B — `from OLD_PARENT import NAME [as ALIAS]` -> `from NEW_PARENT import NAME [as ALIAS]`
    #             (NAME = sous-module déplacé ; la forme dominante du dépôt)
    pats_b = [
        (re.compile(r"(?m)^(\s*from\s+)" + re.escape(op) + r"(\s+import\s+)" + re.escape(name) + r"(?![\w])"),
         r"\1" + np_ + r"\2" + name)
        for (op, name), np_ in fmap.items()
    ]
    changed = 0
    for f in _all_py():
        txt = f.read_text(encoding="utf-8")
        new = txt
        for pat, n in pats_a + pats_b:
            new = pat.sub(n, new)
        if new != txt:
            changed += 1
            if not dry:
                f.write_text(new, encoding="utf-8")
    print(f"  imports réécrits dans {changed} fichier(s){' (simulé)' if dry else ''}")
    print("  -> relire, puis: pytest --co -q ; tests du paquet ; commit" if not dry else "  (dry-run, aucun changement)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
