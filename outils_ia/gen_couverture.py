#!/usr/bin/env python3
"""Genere COUVERTURE_CHAP_<X>.md depuis le JSON d'un audit page-par-page."""
import sys
import json

out, v9, chap = sys.argv[1], sys.argv[2], sys.argv[3]
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


secs = find_sections(parse_any(raw))
if secs is None:
    print("ECHEC: pas de 'sections'")
    sys.exit(2)

sta = {"clos": 0, "partiel": 0, "manquant": 0, "non_applicable": 0}
fid = {"fidele": 0, "ecart_mineur": 0, "ecart_majeur": 0, "non_verifiable": 0}
total = 0
for s in secs:
    for n in s.get("notions", []):
        total += 1
        sta[n.get("code_statut", "manquant")] = sta.get(n.get("code_statut", "manquant"), 0) + 1
        fid[n.get("fidelite", "non_verifiable")] = fid.get(n.get("fidelite", "non_verifiable"), 0) + 1

L = []
L.append("# Couverture %s -- audit page-par-page du texte principal (2026-06-24)" % chap)
L.append("")
L.append("Chaque notion du livre (texte principal) confrontee au code V9. Source = PDF lu page par page.")
L.append("")
L.append("## Synthese (%d notions recensees)" % total)
L.append("")
L.append("**Statut code** : clos %d | partiel %d | **manquant %d** | n/a %d"
         % (sta["clos"], sta["partiel"], sta["manquant"], sta["non_applicable"]))
L.append("")
L.append("**Fidelite** : fidele %d | ecart mineur %d | **ecart majeur %d** | non-verif %d"
         % (fid["fidele"], fid["ecart_mineur"], fid["ecart_majeur"], fid["non_verifiable"]))
L.append("")
# ecarts majeurs
maj = [(s.get("section", "?"), n) for s in secs for n in s.get("notions", []) if n.get("fidelite") == "ecart_majeur"]
L.append("## Ecarts MAJEURS (enonce formalise != Bourbaki) -- priorite")
L.append("")
if not maj:
    L.append("_Aucun._")
for sec, n in maj:
    L.append("- **%s** -- %s (%s) : %s" % (sec[:30], n.get("notion", "?")[:70], n.get("ref", ""), n.get("note", "")[:200]))
L.append("")
# manquants par section
L.append("## Notions MANQUANTES (dans le livre, pas closes dans le code)")
L.append("")
for s in secs:
    mq = [n for n in s.get("notions", []) if n.get("code_statut") == "manquant"]
    if mq:
        L.append("### %s" % s.get("section", "?")[:60])
        for n in mq:
            L.append("- [%s] %s (%s) -- %s" % (n.get("type", "?"), n.get("notion", "?")[:80], n.get("ref", ""), n.get("note", "")[:140]))
        L.append("")
# detail complet
L.append("## Detail complet par section")
L.append("")
for s in secs:
    L.append("### %s" % s.get("section", "?"))
    L.append("_pages : %s_  (%d notions, %d manquantes)" % (
        s.get("pages_lues", "?")[:80], s.get("n_notions", len(s.get("notions", []))),
        s.get("n_manquantes", 0)))
    L.append("")
    L.append("> %s" % s.get("synthese", ""))
    L.append("")
    L.append("| notion | type | ref | statut | fidelite | ou |")
    L.append("|---|---|---|---|---|---|")
    for n in s.get("notions", []):
        L.append("| %s | %s | %s | %s | %s | %s |" % (
            n.get("notion", "?")[:55].replace("|", "/"), n.get("type", ""), n.get("ref", ""),
            n.get("code_statut", ""), n.get("fidelite", ""),
            (n.get("ou_dans_code", "") or "")[:40].replace("|", "/")))
    L.append("")
open(v9 + "/COUVERTURE_%s.md" % chap, "w", encoding="utf-8").write("\n".join(L))
print("COUVERTURE_%s.md : %d notions, clos %d, partiel %d, manquant %d, ecart_majeur %d"
      % (chap, total, sta["clos"], sta["partiel"], sta["manquant"], fid["ecart_majeur"]))
