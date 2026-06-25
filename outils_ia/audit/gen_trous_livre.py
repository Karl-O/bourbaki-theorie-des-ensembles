#!/usr/bin/env python3
"""Détecteur de trous de couverture par collation des marqueurs ``@livre``.

Chaque notion formalisée porte, juste au-dessus de sa ``def``, un commentaire :

    # @livre Ch.<C> §<s> <Type>.<num> | <repère Bourbaki> L.<l1>-<l2> | PDF p.<phys>

Cet outil scanne l'arbre ``bourbaki/``, lit tous ces marqueurs, les trie par
(chapitre, page physique, ligne), et fait apparaître les TROUS : sur une même
page du livre, un intervalle de lignes situé entre deux notions consécutives et
non couvert signale une notion probablement oubliée. *La citation est le
détecteur de trous.*

Usage :
    python outils_ia/audit/gen_trous_livre.py [racine=bourbaki] [--md sortie.md]

Sortie : un rapport texte (stdout) et, en option, une carte Markdown.
Le code de sortie vaut 0 si au moins un marqueur est trouvé, 1 sinon (utile en CI
pour gater « la section X doit être annotée »).
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

# # @livre Ch.II §6.4 Prop.- | E II.43 L.31-32 | PDF p.94
_RE = re.compile(
    r"#\s*@livre\s+"
    r"Ch\.(?P<chap>\S+)\s+"          # II
    r"§(?P<sec>\S+)\s+"              # 6.4
    r"(?P<type>\w+)\.(?P<num>\S+)"   # Prop.-
    r"\s*\|\s*"
    r"(?P<repere>.+?)\s+"            # E II.43   (repère imprimé du livre)
    r"L\.(?P<l1>\d+)-(?P<l2>\d+)"    # L.31-32
    r"\s*\|\s*"
    r"PDF\s+p\.(?P<phys>\d+)"        # PDF p.94
)

# Ordre canonique des chapitres (pour le tri ; R = Résumé).
_ORDRE_CHAP = {"I": 1, "II": 2, "III": 3, "IV": 4, "R": 5}


class Marqueur:
    __slots__ = ("chap", "sec", "type", "num", "repere", "l1", "l2",
                 "phys", "fichier", "ligne", "notion")

    def __init__(self, m: re.Match, fichier: Path, ligne: int, notion: str):
        self.chap = m["chap"]
        self.sec = m["sec"]
        self.type = m["type"]
        self.num = m["num"]
        self.repere = m["repere"].strip()
        self.l1 = int(m["l1"])
        self.l2 = int(m["l2"])
        self.phys = int(m["phys"])
        self.fichier = fichier
        self.ligne = ligne
        self.notion = notion

    @property
    def cle_tri(self):
        return (_ORDRE_CHAP.get(self.chap, 99), self.phys, self.l1, self.l2)


def _notion_suivante(lignes: list[str], i: int) -> str:
    """Nom de la def/class qui suit le marqueur à l'indice i (sinon '?')."""
    for j in range(i + 1, min(i + 4, len(lignes))):
        m = re.match(r"\s*(?:def|class)\s+(\w+)", lignes[j])
        if m:
            return m.group(1)
    return "?"


def collecter(racine: Path) -> list[Marqueur]:
    marqueurs: list[Marqueur] = []
    for f in sorted(racine.rglob("*.py")):
        if "__pycache__" in f.parts:
            continue
        try:
            lignes = f.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeDecodeError):
            continue
        for i, ligne in enumerate(lignes):
            if "@livre" not in ligne:
                continue
            m = _RE.search(ligne)
            if m:
                marqueurs.append(
                    Marqueur(m, f, i + 1, _notion_suivante(lignes, i)))
    return marqueurs


def trouver_trous(marqueurs: list[Marqueur]) -> list[tuple]:
    """Trous = intervalles de lignes non couverts entre deux notions
    consécutives d'une MÊME page physique. Retourne (chap, phys, gl1, gl2,
    avant, apres)."""
    trous = []
    par_page: dict[tuple, list[Marqueur]] = {}
    for mq in marqueurs:
        par_page.setdefault((mq.chap, mq.phys), []).append(mq)
    for (chap, phys), groupe in par_page.items():
        groupe.sort(key=lambda x: (x.l1, x.l2))
        for a, b in zip(groupe, groupe[1:]):
            # chevauchement ou contiguïté toléré ; trou si b commence > a.l2 + 1
            if b.l1 > a.l2 + 1:
                trous.append((chap, phys, a.l2 + 1, b.l1 - 1, a.notion, b.notion))
    return trous


def rapport_texte(marqueurs: list[Marqueur], trous: list[tuple]) -> str:
    out = []
    out.append(f"Marqueurs @livre trouvés : {len(marqueurs)}")
    out.append("")
    chap_courant = phys_courant = None
    for mq in sorted(marqueurs, key=lambda x: x.cle_tri):
        if mq.chap != chap_courant:
            chap_courant = mq.chap
            phys_courant = None
            out.append(f"=== Chapitre {mq.chap} ===")
        if mq.phys != phys_courant:
            phys_courant = mq.phys
            out.append(f"  -- {mq.repere}  (PDF p.{mq.phys}) --")
        out.append(f"     L.{mq.l1:>3}-{mq.l2:<3} §{mq.sec:<6} "
                   f"{mq.type}.{mq.num:<4} {mq.notion}")
    out.append("")
    if trous:
        out.append(f"TROUS POTENTIELS ({len(trous)}) "
                   f"— lignes non couvertes entre deux notions d'une même page :")
        for chap, phys, gl1, gl2, av, ap in sorted(trous):
            out.append(f"  Ch.{chap} PDF p.{phys} : L.{gl1}-{gl2} non couvert "
                       f"(entre « {av} » et « {ap} »)")
    else:
        out.append("Aucun trou intra-page détecté (couverture contiguë sur "
                   "chaque page annotée).")
    return "\n".join(out)


def rapport_markdown(marqueurs: list[Marqueur], trous: list[tuple]) -> str:
    out = ["# Carte de couverture `@livre`", "",
           f"- Marqueurs : **{len(marqueurs)}**",
           f"- Trous intra-page potentiels : **{len(trous)}**", "",
           "| Chap | Repère | PDF | Lignes | § | Type | Notion |",
           "|------|--------|-----|--------|---|------|--------|"]
    for mq in sorted(marqueurs, key=lambda x: x.cle_tri):
        out.append(f"| {mq.chap} | {mq.repere} | p.{mq.phys} | "
                   f"L.{mq.l1}-{mq.l2} | {mq.sec} | {mq.type}.{mq.num} | "
                   f"`{mq.notion}` |")
    if trous:
        out += ["", "## Trous potentiels", ""]
        for chap, phys, gl1, gl2, av, ap in sorted(trous):
            out.append(f"- **Ch.{chap} PDF p.{phys}** : L.{gl1}-{gl2} non "
                       f"couvert (entre `{av}` et `{ap}`)")
    return "\n".join(out) + "\n"


def main(argv: list[str]) -> int:
    racine = Path("bourbaki")
    sortie_md = None
    rest = list(argv)
    if "--md" in rest:
        k = rest.index("--md")
        sortie_md = Path(rest[k + 1])
        del rest[k:k + 2]
    if rest:
        racine = Path(rest[0])
    if not racine.exists():
        print(f"racine introuvable : {racine}", file=sys.stderr)
        return 2

    marqueurs = collecter(racine)
    trous = trouver_trous(marqueurs)
    print(rapport_texte(marqueurs, trous))
    if sortie_md is not None:
        sortie_md.write_text(rapport_markdown(marqueurs, trous), encoding="utf-8")
        print(f"\nCarte Markdown écrite : {sortie_md}")
    return 0 if marqueurs else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
