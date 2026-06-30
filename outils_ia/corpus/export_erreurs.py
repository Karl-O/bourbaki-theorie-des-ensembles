#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Export des TRACES D'ERREURS = exemples NÉGATIFS du dataset (pivot méta-algo, pas 3b).

Un générateur generate-and-verify n'a pas que besoin de bonnes preuves : il lui faut
aussi des **marches mortes étiquetées** — les approches qui ÉCHOUENT et POURQUOI. Le
projet les documente déjà (exigence « documenter le pourquoi/les erreurs autant que les
preuves ») dans `docs/journal/DECISIONS.md` et `ANOMALIES.md` : tautologies déguisées
rejetées, verrous de capture-τ, specs fausses bloquées par le noyau, écarts de fidélité…

On parse ces journaux markdown (sections `### …`) en un JSONL d'exemples négatifs :
  { source, title, body, labels:[...] }
où `labels` classe l'entrée par heuristique (rejet / verrou-τ / capture / fidélité /
résolu / choix-bloqué). Données idéales pour pénaliser/éviter ces patterns côté générateur.

USAGE : python outils_ia/corpus/export_erreurs.py > erreurs.jsonl
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
JOURNAUX = [_V9 / "docs" / "journal" / "DECISIONS.md",
            _V9 / "docs" / "journal" / "ANOMALIES.md"]

# (motif regex insensible casse, étiquette)
_LABELS = [
    (r"tautologie|d[ée]guis", "tautologie-rejetee"),
    (r"verrou|capture|τ-|alpha|α-renomm", "verrou-tau"),
    (r"choix|choice|axiome du choix", "choix-bloque"),
    (r"fid[ée]lit|@livre|faut[ie]f|p[ée]rim", "fidelite"),
    (r"r[ée]solu|corrig", "resolu"),
    (r"rejet|REJET|non commit|supprim", "rejet"),
    (r"le[çc]on|le[cç]on|LE[ÇC]ON", "lecon"),
]


def _sections(md: str):
    """Découpe un markdown en (titre, corps) sur les en-têtes `### `."""
    parts = re.split(r"(?m)^###\s+(.+)$", md)
    # parts = [avant, titre1, corps1, titre2, corps2, ...]
    for i in range(1, len(parts), 2):
        titre = parts[i].strip()
        corps = parts[i + 1].strip() if i + 1 < len(parts) else ""
        yield titre, corps


def _labels(texte: str) -> list[str]:
    bas = texte.lower()
    return [lab for pat, lab in _LABELS if re.search(pat, bas, re.IGNORECASE)]


def main() -> int:
    records = []
    for chemin in JOURNAUX:
        if not chemin.exists():
            print(f"# absent : {chemin}", file=sys.stderr)
            continue
        md = chemin.read_text(encoding="utf-8")
        for titre, corps in _sections(md):
            if not corps:
                continue
            records.append({
                "source": chemin.name,
                "title": titre,
                "body": corps,
                "labels": _labels(titre + " " + corps),
                "polarite": "negatif",          # exemple négatif / leçon
            })
    for r in records:
        print(json.dumps(r, ensure_ascii=False))
    import collections
    labs = collections.Counter(l for r in records for l in r["labels"])
    print(f"# TOTAL : {len(records)} entrées-erreur ; labels {dict(labs)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
