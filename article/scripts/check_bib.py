"""Cohérence bibliographique de l'article (ce que l'ancre Related Work promettait).

Vérifie :
  • toute clé citée dans main.tex existe dans references.bib ;
  • toute entrée de references.bib est effectivement citée ;
  • rappelle les claims que RELATED.md demande de recentrer.

Usage :  python article/scripts/check_bib.py     (code de sortie 1 si incohérence)
"""
import io
import pathlib
import re
import sys

BASE = pathlib.Path(__file__).resolve().parent.parent


def main():
    tex = io.open(BASE / "main.tex", encoding="utf-8").read()
    bib = io.open(BASE / "references.bib", encoding="utf-8").read()

    cites = set()
    for m in re.finditer(r"\\cite\{([^}]*)\}", tex):
        cites |= {c.strip() for c in m.group(1).split(",")}
    keys = set(re.findall(r"@\w+\{([^,]+),", bib))

    manquantes, orphelines = sorted(cites - keys), sorted(keys - cites)
    print("citées non définies :", manquantes or "aucune")
    print("définies non citées :", orphelines or "aucune")
    print(f"total : {len(cites)} citées, {len(keys)} définies")

    rel_p = BASE / "RELATED.md"
    if rel_p.exists():
        rel = io.open(rel_p, encoding="utf-8").read()
        m = re.search(r"RECENTR[ÉE]S?\s*\(([^)]*)\)", rel)
        if m:
            print("\nRELATED.md — claims à recentrer :", m.group(1))
    return 1 if (manquantes or orphelines) else 0


if __name__ == "__main__":
    sys.exit(main())
