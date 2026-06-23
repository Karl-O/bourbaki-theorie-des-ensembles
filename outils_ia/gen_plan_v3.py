#!/usr/bin/env python3
"""Génère PLAN_ETAPE_B_v3.md depuis le JSON résultat de l'audit fan-out."""
import sys
import json

out, v9 = sys.argv[1], sys.argv[2]
raw = open(out, encoding="utf-8", errors="replace").read()


def parse_any(s):
    try:
        return json.loads(s)
    except Exception:
        for ln in s.splitlines():
            if '"sections"' in ln:
                try:
                    return json.loads(ln)
                except Exception:
                    pass
    return None


def find_sections(o):
    """Cherche récursivement une liste sous la clé 'sections'."""
    if isinstance(o, dict):
        if isinstance(o.get("sections"), list):
            return o["sections"]
        for v in o.values():
            r = find_sections(v)
            if r is not None:
                return r
    elif isinstance(o, list):
        for v in o:
            r = find_sections(v)
            if r is not None:
                return r
    return None


obj = parse_any(raw)
secs = find_sections(obj)
if secs is None:
    print("ECHEC: pas de 'sections' trouve")
    sys.exit(2)
ordre = {"faible/facile": 0, "faible/moyen": 1, "moyen/moyen": 2, "moyen/difficile": 3}

cibles = []
for s in secs:
    sec = s.get("section", "?").split("—")[0].strip()
    for c in s.get("cibles", []):
        c["_sec"] = sec
        cibles.append(c)
cibles.sort(key=lambda c: ordre.get(c.get("difficulte", ""), 9))


def rel(p):
    p = (p or "").replace(chr(92), "/")
    i = p.find("/V9/")
    return p[i + 4:] if i >= 0 else p


lines = [
    "# PLAN ETAPE B v3 -- nouveau lot de cibles faisables (audit fan-out w1k1qywh0)",
    "",
    "Issu de l'audit par section (6 agents). %d cibles candidates, triees faible->moyen." % len(cibles),
    "Format : `## [ ] <nom>` a cocher `## [x]` APRES commit. Verifier l'existence des lemmes avant delegation.",
    "",
]
for c in cibles:
    lines.append("## [ ] %s  (%s)" % (c.get("nom", "?"), c.get("difficulte", "?")))
    lines.append("- secteur: %s  | %s" % (c.get("_sec", "?"), c.get("ref", "?")))
    lines.append("- statut: %s" % c.get("statut", "?"))
    lines.append("- enonce: %s" % c.get("enonce", "?"))
    lines.append("- strategie: %s" % c.get("strategie", "?"))
    lines.append("- lemmes: %s" % c.get("lemmes", "?"))
    lines.append("- fichier: %s" % rel(c.get("fichier", "?")))
    lines.append("")
open(v9 + "/PLAN_ETAPE_B_v3.md", "w", encoding="utf-8").write("\n".join(lines))

print("CIBLES (triees):")
for i, c in enumerate(cibles):
    print("%2d. [%-14s] %-6s %-42s <- %s" % (
        i + 1, c.get("difficulte", "?"), c.get("_sec", "?"),
        c.get("nom", "?"), rel(c.get("fichier", "?"))[:58]))
