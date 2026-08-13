"""Audit des listes REPORTES : détecte les reports PÉRIMÉS.

────────────────────────────────────────────────────────────────────────────────
Motivation (leçon des 3-4 août 2026 : trois reports périmés trouvés à la main —
Prop. 1 1°, Prop. 1 2°, Prop. 10).  Une entrée de `REPORTES` vieillit mal : le
théorème finit par être démontré ailleurs, et la liste continue de le déclarer
ouvert — on risque alors de RÉÉCRIRE un acquis.

Cet outil croise, pour chaque entrée de REPORTES du dépôt :
  • le REPÈRE du livre qu'elle cite  (« Prop. 10 », « §III.1.10 », « Th. 1 »…) ;
  • les marqueurs `@livre` du dépôt portant le MÊME repère (chapitre + type +
    numéro), et les `def` qu'ils annoncent.
Verdict par entrée :
  SUSPECT   — un module PORTE ce repère avec des définitions, et le texte du
              report ne mentionne aucune résolution : probablement périmé
              → À VÉRIFIER EN CODE (import + appel).
  RÉSOLU    — le texte porte déjà une annotation de résolution (« ✅ », « FAIT »,
              « n'est plus reporté ») : entrée à jour, rien à faire.
  OK        — aucun module ne porte ce repère : le report est plausible.
Le verdict SUSPECT n'est jamais une preuve : il désigne quoi tester, l'outil ne
décide pas à la place du noyau.

Usage :  python outils_ia/audit/audit_reports.py  [--tout]
         (--tout affiche aussi les entrées OK)
"""
from __future__ import annotations

import argparse
import ast
import pathlib
import re
import sys

RACINE = pathlib.Path(__file__).resolve().parents[2] / "bourbaki"

# « Ch.III §1.10 Prop.10 » dans un @livre  /  « Proposition 10 (§III.1.10) » en prose
RE_LIVRE = re.compile(r"@livre\s+Ch\.(\w+)\s+§([\d.]+)\s+(\w+)\.([\d\-]+|-)")
RE_TYPE = {"Prop": "Prop", "Proposition": "Prop", "Th": "Th", "Théorème": "Th",
           "Theoreme": "Th", "Cor": "Cor", "Corollaire": "Cor", "Lem": "Lem",
           "Lemme": "Lem", "Crit": "Crit", "Critère": "Crit"}
RE_REPERE = re.compile(
    r"(Proposition|Prop\.|Théorème|Th\.|Corollaire|Cor\.|Lemme|Lem\.|Critère|Crit\.)"
    r"\s*(\d+)")
RE_SECTION = re.compile(r"§\s*([IVX]+)\.([\d.]+)")


def _fichiers():
    for p in sorted(RACINE.rglob("*.py")):
        if "__pycache__" not in p.parts:
            yield p


def collecte_reports():
    """[(fichier, texte_du_report)] — les entrées littérales des listes REPORTES."""
    out = []
    for p in _fichiers():
        src = p.read_text(encoding="utf-8", errors="replace")
        if "REPORTES" not in src:
            continue
        try:
            arbre = ast.parse(src)
        except SyntaxError:
            continue
        for noeud in ast.walk(arbre):
            if not isinstance(noeud, ast.Assign):
                continue
            cibles = [t.id for t in noeud.targets if isinstance(t, ast.Name)]
            if "REPORTES" not in cibles or not isinstance(noeud.value, ast.List):
                continue
            for elt in noeud.value.elts:
                if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
                    out.append((p, " ".join(elt.value.split())))
    return out


def index_livre():
    """{(chap, section, Type, num) : [(fichier, def)]} — tous les @livre du dépôt.

    La SECTION fait partie de la clé : sans elle, « Prop. 5 » de §III.7.4
    matcherait celle de §III.1 (faux positif observé au premier essai)."""
    idx = {}
    for p in _fichiers():
        lignes = p.read_text(encoding="utf-8", errors="replace").splitlines()
        for n, ligne in enumerate(lignes):
            m = RE_LIVRE.search(ligne)
            if not m:
                continue
            chap, sec, typ, num = m.groups()
            if num == "-":
                continue
            nom_def = ""
            for suite in lignes[n + 1:n + 6]:
                if suite.lstrip().startswith("def "):
                    nom_def = suite.split("def ", 1)[1].split("(")[0]
                    break
            cle = (chap, sec, RE_TYPE.get(typ, typ), num)
            idx.setdefault(cle, []).append((p, nom_def))
    return idx


def repere_du_report(texte):
    """(chap, section, Type, num) cité par un report, ou None si illisible.

    La section est OBLIGATOIRE : un report qui ne la cite pas n'est pas
    localisable, donc jamais déclaré suspect (silence prudent)."""
    mt = RE_REPERE.search(texte)
    ms = RE_SECTION.search(texte)
    if not mt or not ms:
        return None
    typ = RE_TYPE.get(mt.group(1).rstrip("."), None)
    return (ms.group(1), ms.group(2), typ, mt.group(2)) if typ else None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--tout", action="store_true", help="afficher aussi les OK")
    args = ap.parse_args(argv)

    reports, idx = collecte_reports(), index_livre()
    suspects = resolus = 0
    marques = ("✅", "FAIT", "n'est plus report", "PÉRIMÉ", "PERIME")
    for fichier, texte in reports:
        rep = repere_du_report(texte)
        porteurs = [(p, d) for (p, d) in idx.get(rep, []) if d] if rep else []
        # un report n'est PAS suspect à cause de son propre module
        porteurs = [(p, d) for (p, d) in porteurs if p != fichier]
        court = texte if len(texte) <= 96 else texte[:93] + "..."
        if any(m in texte for m in marques):
            resolus += 1
            if args.tout:
                print(f"RÉSOLU   {fichier.relative_to(RACINE.parent)} — « {court} »")
        elif porteurs:
            suspects += 1
            print(f"SUSPECT  {fichier.relative_to(RACINE.parent)}")
            print(f"         « {court} »")
            for p, d in porteurs[:3]:
                print(f"         ↳ porté par {p.relative_to(RACINE.parent)} : {d}()")
        elif args.tout:
            print(f"OK       {fichier.relative_to(RACINE.parent)} — « {court} »")
    print(f"\n{len(reports)} reports examinés — {suspects} SUSPECT(S) à vérifier "
          f"en code (import + appel) avant tout effort, {resolus} déjà annoté(s) résolu(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
