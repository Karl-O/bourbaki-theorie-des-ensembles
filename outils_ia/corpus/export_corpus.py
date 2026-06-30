#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Export du CORPUS de preuves V9 comme dataset generate-and-verify (méta-algo).

PREMIER PAS du pivot méta-algo (cf. docs/couverture/STATUT_REEL_2026-06-30.md).
But : transformer le corpus Bourbaki formalisé (≈616 modules, ≈939 traces @livre)
en un dataset où chaque exemple est une paire

    (BUT = énoncé du théorème)  ⟶  (PREUVE = programme N.* qui le construit)

avec le NOYAU LCF comme vérificateur exact : ré-exécuter la preuve et vérifier
conclusion == but. C'est la donnée d'entraînement d'un générateur generate-and-verify
(GFlowNet sur DAG de tactiques / diffusion discrète + filtre-kernel).

CE QU'ON EXPORTE (par théorème) — un objet JSON par ligne (JSONL) :
  · name, module           : identité de la fonction-théorème ;
  · livre                  : marqueur @livre (chapitre/§/page PDF) — ancre vers le livre ;
  · clos, justification    : statut (clos/conditionnel) + dernière règle noyau appliquée ;
  · n_hyp                  : nb d'hypothèses honnêtes (0 si clos) ;
  · conclusion_ast         : repr canonique de la formule-but (AST fidèle, ré-parsable) ;
  · hypotheses_ast         : idem pour chaque hypothèse ;
  · proof_src              : SOURCE de la fonction = le PROGRAMME-preuve (la trajectoire) ;
  · verified               : True si on a pu RÉ-vérifier conclusion == cible (companion *_cible)
                             ou au moins reconstruire le théorème par appel.

LIMITE (assumée) de cette V1 : `Theoreme` ne stocke pas ses prémisses (slots =
hypotheses/conclusion/justification), donc le DAG d'inférence fin n'est pas dans
l'objet. On capture la preuve au niveau du PROGRAMME (source). Étape suivante :
instrumenter les primitives N.* pour journaliser la trace (règle, entrées, sortie)
et obtenir la trajectoire pas-à-pas — la vraie « marche sur le DAG ».

USAGE : python outils_ia/corpus/export_corpus.py [module1 module2 ...] > sortie.jsonl
        (sans argument : liste fast par défaut, ÉVITE les imports cardinaux lents.)
"""
from __future__ import annotations

import importlib
import inspect
import json
import re
import sys
from pathlib import Path

# Racine V9 (contient `bourbaki/`) sur le sys.path, que le script soit lancé d'où que ce soit.
_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from trace_preuve import tracer_theoreme   # noqa: E402  (tracer la trajectoire pas-à-pas)

_LIVRE_RE = re.compile(r"#\s*@livre\s+(.+)")

# Liste « fast » par défaut (imports légers, pas de cardinaux 13-18 min).
MODULES_FAST = [
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_couples",
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_couple_caracterisation",
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_projection_fonctionnelle",
    "bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide",
    "bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple",
    "bourbaki.ensembles.ii_3_correspondances.ensembles_identite_neutre",
    "bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee_monotone",
    "bourbaki.logique.i_3_quantifies.criteres_typiques_c41",
]


def _livre_au_dessus(file_lines: list[str], start_lineno: int) -> str | None:
    """Cherche un marqueur @livre dans les ~6 lignes au-dessus de la def (1-based)."""
    for i in range(start_lineno - 2, max(start_lineno - 9, -1), -1):
        if 0 <= i < len(file_lines):
            m = _LIVRE_RE.search(file_lines[i])
            if m:
                return m.group(1).strip()
    return None


def _est_theoreme(obj) -> bool:
    return type(obj).__name__ == "Theoreme" and hasattr(obj, "conclusion")


def exporter_module(modname: str, records: list[dict]) -> tuple[int, int]:
    """Ajoute un record par fonction-théorème appelable du module. (faits, sautés)."""
    mod = importlib.import_module(modname)
    fichier = inspect.getsourcefile(mod)
    with open(fichier, encoding="utf-8") as fh:
        file_lines = fh.read().splitlines()
    noms = list(getattr(mod, "__all__", [n for n in dir(mod) if not n.startswith("_")]))
    faits = sautes = 0
    for name in noms:
        fn = getattr(mod, name, None)
        if not inspect.isfunction(fn) or fn.__module__ != modname:
            continue
        if name.endswith("_cible") or name.startswith("theorie_") or name.startswith("axiome_"):
            continue
        try:
            thm, steps = tracer_theoreme(fn)             # appel + trajectoire pas-à-pas
        except Exception:
            sautes += 1
            continue
        if not _est_theoreme(thm):
            sautes += 1
            continue
        rule_hist: dict[str, int] = {}
        for st in steps:
            rule_hist[st["rule"]] = rule_hist.get(st["rule"], 0) + 1
        # vérif : si un companion <name>_cible existe, comparer conclusion == cible
        verified = None
        cible_fn = getattr(mod, name + "_cible", None) or getattr(mod, "cible_" + name, None)
        if callable(cible_fn):
            try:
                verified = (thm.conclusion == cible_fn())
            except Exception:
                verified = None
        try:
            proof_src = inspect.getsource(fn)
            _, start = inspect.getsourcelines(fn)
        except Exception:
            proof_src, start = None, None
        livre = _livre_au_dessus(file_lines, start) if start else None
        records.append({
            "name": name,
            "module": modname,
            "livre": livre,
            "clos": thm.est_clos,
            "justification": thm.justification,
            "n_hyp": len(thm.hypotheses),
            "conclusion_ast": repr(thm.conclusion),
            "hypotheses_ast": sorted(repr(h) for h in thm.hypotheses),
            "proof_src": proof_src,
            "verified": verified,
            "trace_len": len(steps),                     # nb de pas primitifs (profondeur DAG)
            "rule_hist": rule_hist,                      # histogramme des règles noyau
        })
        faits += 1
    return faits, sautes


def main(argv: list[str]) -> int:
    modules = argv[1:] or MODULES_FAST
    records: list[dict] = []
    faits_tot = sautes_tot = 0
    for m in modules:
        try:
            f, s = exporter_module(m, records)
            faits_tot += f
            sautes_tot += s
            print(f"# {m}: {f} théorèmes, {s} sautés", file=sys.stderr)
        except Exception as e:                           # import cassé / module absent
            print(f"# {m}: ERREUR {type(e).__name__}: {e}", file=sys.stderr)
    for r in records:
        print(json.dumps(r, ensure_ascii=False))
    print(f"# TOTAL: {faits_tot} théorèmes exportés, {sautes_tot} sautés, "
          f"{len(modules)} modules", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
