#!/usr/bin/env python3
"""Genere FIDELITE_PDF.md depuis le JSON resultat de l'audit de fidelite PDF."""
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

# compteurs globaux
fid = {"fidele": 0, "ecart_mineur": 0, "ecart_majeur": 0, "non_verifiable": 0}
sta = {"formalise_clos": 0, "formalise_partiel": 0, "manquant": 0, "non_applicable": 0}
total = 0
for s in secs:
    for n in s.get("notions", []):
        total += 1
        fid[n.get("fidelite", "non_verifiable")] = fid.get(n.get("fidelite", "non_verifiable"), 0) + 1
        sta[n.get("code_statut", "manquant")] = sta.get(n.get("code_statut", "manquant"), 0) + 1

L = []
L.append("# Audit de FIDÉLITÉ au PDF Bourbaki — Résumé des résultats (2026-06-24)")
L.append("")
L.append("Comparaison notion-par-notion : texte du livre (Résumé des résultats, PDF) ↔ formalisation V9.")
L.append("⚠ Source = Résumé (énoncés condensés, SANS preuves, OMET le Chap. I) ; à compléter par le texte principal.")
L.append("")
L.append("## Synthèse globale (%d notions auditées)" % total)
L.append("")
L.append("**Fidélité** : fidèle %d · écart mineur %d · **écart majeur %d** · non vérifiable %d"
         % (fid["fidele"], fid["ecart_mineur"], fid["ecart_majeur"], fid["non_verifiable"]))
L.append("")
L.append("**Statut code** : clos %d · partiel %d · **manquant %d** · n/a %d"
         % (sta["formalise_clos"], sta["formalise_partiel"], sta["manquant"], sta["non_applicable"]))
L.append("")
# liste prioritaire : ecarts majeurs puis manquants
L.append("## ⚠ Écarts MAJEURS (énoncé formalisé ≠ Bourbaki) — à corriger en priorité")
L.append("")
maj = [(s.get("section", "?"), n) for s in secs for n in s.get("notions", []) if n.get("fidelite") == "ecart_majeur"]
if not maj:
    L.append("_Aucun écart majeur détecté._")
else:
    for sec, n in maj:
        L.append("- **%s** — %s (%s) : %s" % (sec[:40], n.get("notion", "?")[:80], n.get("er_page", ""), n.get("note", "")))
L.append("")
L.append("## Notions MANQUANTES (dans le livre, pas dans le code)")
L.append("")
for s in secs:
    mq = [n for n in s.get("notions", []) if n.get("code_statut") == "manquant"]
    if mq:
        L.append("### %s" % s.get("section", "?"))
        for n in mq:
            L.append("- %s (%s) — %s" % (n.get("notion", "?")[:90], n.get("er_page", ""), n.get("note", "")[:160]))
        L.append("")
# detail complet par section
L.append("## Détail complet par section")
L.append("")
for s in secs:
    L.append("### %s" % s.get("section", "?"))
    L.append("_pages lues : %s_" % s.get("pages_lues", "?"))
    L.append("")
    L.append("> %s" % s.get("synthese", ""))
    L.append("")
    L.append("| notion | E.R. | statut | fidélité |")
    L.append("|---|---|---|---|")
    for n in s.get("notions", []):
        L.append("| %s | %s | %s | %s |" % (
            n.get("notion", "?")[:70].replace("|", "/"), n.get("er_page", ""),
            n.get("code_statut", ""), n.get("fidelite", "")))
    L.append("")
open(v9 + "/FIDELITE_PDF.md", "w", encoding="utf-8").write("\n".join(L))
print("FIDELITE_PDF.md ecrit : %d notions, %d ecarts majeurs, %d manquants"
      % (total, fid["ecart_majeur"], sta["manquant"]))
print("Fidelite:", fid)
print("Statut:", sta)
