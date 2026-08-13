# -*- coding: utf-8 -*-
"""Audit des TERMES OPAQUES : quels `app("nom", …)` ne sont caractérisés par rien ?

────────────────────────────────────────────────────────────────────────────────
POURQUOI.  Le dépôt introduit ses objets de deux façons : soit en les
CONSTRUISANT (`graphe_terme`, réunion, produit…), soit en posant un terme opaque
`app("nom", args)` que l'on caractérise ensuite par un axiome définitionnel.  Un
terme opaque *avec* axiome est utilisable — on peut en déduire ses propriétés.
Un terme opaque *sans* axiome ne l'est pas : **tout énoncé qui le mentionne est
indémontrable**, et rien ne le signale.  C'est une impasse silencieuse : elle ne
se révèle qu'au moment où l'on tente un raccord, parfois très loin en aval.

Cas fondateurs.  `restriction_systeme_indices` = app("restr_indices", E, f, J),
sans aucun axiome, alors que lim←_J := lim_proj(restr_indices(…), f) : aucun
énoncé sur lim←_J n'était démontrable — pas par difficulté, par construction
(4 août 2026).  Puis `M_indice`, accesseur opaque de la famille de PARTIES, qui
bloquait de la même façon la 2ᵉ assertion de la Prop. 2 (5 août).  Dans les deux
cas le remède est identique, et c'est celui de `application_canonique_g` :
CONSTRUIRE l'objet au lieu de le postuler — ici, reconnaître qu'une famille EST
une fonction, donc que sa composante EST sa valeur.

CE QUE MESURE CET OUTIL, ET CE QU'IL NE MESURE PAS.
Pour chaque constructeur, on remonte à sa (ses) FONCTION(S) ENVELOPPE — celle
dont le corps écrit `app("nom", …)` — car les axiomes référencent l'enveloppe,
jamais la chaîne brute.

DEUX FAUX POSITIFS VÉCUS, tous deux corrigés — ils disent comment lire un audit :
  • chercher le nom BRUT dans les axiomes donnait 112 « sans axiome » sur 146,
    parce que les axiomes citent l'ENVELOPPE.  Un audit qui remonte trop peu de
    niveaux produit surtout du bruit ;
  • scanner le TEXTE comptait les `app("nom", …)` cités dans les DOCSTRINGS.
    L'outil signalait donc encore `M_indice` APRÈS sa correction — un audit qui
    crie au loup sur ses propres corrections perd toute valeur.  D'où la lecture
    par AST.  (Le compte est passé de 144 à 113 constructeurs : l'écart était
    entièrement du bruit.)

« Non caractérisé » ici veut dire : ni l'enveloppe ni le nom n'apparaissent dans
un `def axiome_*`, un `def theorie_*` ou un `AXIOME_*`.  Ce n'est PAS une preuve
d'impasse : beaucoup de ces termes sont des TÉMOINS LOCAUX (un seul fichier,
introduits et consommés sur place dans une preuve — Zorn, Zermelo,
Bourbaki-Witt…), et d'autres sont caractérisés par des THÉORÈMES plutôt que par
un axiome.  D'où la colonne décisive : le nombre de fichiers.  **Un terme non
caractérisé ET partagé entre plusieurs fichiers est le vrai signal** — il a
vocation à être raccordé, donc l'impasse finira par se manifester.

USAGE :  python outils_ia/audit/audit_termes_opaques.py [--tous]
"""
from __future__ import annotations

import ast
import collections
import pathlib
import re
import sys

RACINE = pathlib.Path(__file__).resolve().parents[2] / "bourbaki"


def _enveloppes_et_sites():
    """constructeur -> (fonctions enveloppes, fichiers où il est écrit).

    ⚠️ Lecture par AST, PAS par expression régulière — corrigé le 5 août 2026
    après une fausse alerte vécue.  La première version scannait le TEXTE : elle
    comptait les `app("nom", …)` cités dans les DOCSTRINGS comme du code, et
    continuait donc à signaler un terme APRÈS sa correction.  Un audit qui crie
    au loup sur ses propres corrections perd toute valeur : on ne visite ici que
    les vrais appels `app("…", …)` de l'arbre syntaxique."""
    env = collections.defaultdict(set)
    sites = collections.defaultdict(set)
    for p in RACINE.rglob("*.py"):
        try:
            arbre = ast.parse(p.read_text(encoding="utf-8", errors="replace"))
        except SyntaxError:
            continue
        for fn in (n for n in ast.walk(arbre)
                   if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))):
            for n in ast.walk(fn):
                if (isinstance(n, ast.Call)
                        and isinstance(n.func, ast.Name) and n.func.id == "app"
                        and n.args and isinstance(n.args[0], ast.Constant)
                        and isinstance(n.args[0].value, str)):
                    env[n.args[0].value].add(fn.name)
                    sites[n.args[0].value].add(str(p.relative_to(RACINE)))
    return env, sites


def _sources_axiomes():
    """Le texte de tous les `def axiome_*`, `def theorie_*` et `AXIOME_* = …`."""
    morceaux = []
    for p in RACINE.rglob("*.py"):
        txt = p.read_text(encoding="utf-8", errors="replace")
        morceaux += [m.group(1) for m in re.finditer(
            r"(def\s+(?:axiome_|theorie_)\w+.*?)(?=\ndef |\Z)", txt, re.S)]
        morceaux += [m.group(1) for m in re.finditer(
            r"(AXIOME_\w+\s*=.*?)(?=\n[A-Za-z_]|\Z)", txt, re.S)]
    return "\n".join(morceaux)


def audit():
    env, sites = _enveloppes_et_sites()
    blob = _sources_axiomes()
    non_carac = []
    for nom, envs in sorted(env.items()):
        if not any(re.search(r"\b" + re.escape(w) + r"\b", blob)
                   for w in set(envs) | {nom}):
            non_carac.append(nom)
    return env, sites, non_carac


def main(tous=False):
    env, sites, non_carac = audit()
    partages = [n for n in non_carac if len(sites[n]) >= 2]
    print(f"{len(env)} constructeurs app(\"…\") ; "
          f"{len(env) - len(non_carac)} caractérisés par un axiome/théorie.")
    print(f"{len(non_carac)} non caractérisés — dont {len(partages)} PARTAGÉS "
          f"entre plusieurs fichiers (le vrai signal).\n")
    print("── non caractérisés ET partagés (à construire, ou à caractériser) ──")
    for n in partages:
        print(f"   {n:26} {len(sites[n])} fichiers | "
              f"enveloppes : {', '.join(sorted(env[n])[:3])}")
    if tous:
        print("\n── non caractérisés, un seul fichier (souvent des témoins locaux) ──")
        for n in non_carac:
            if n not in partages:
                print(f"   {n:26} {sorted(sites[n])[0]}")
    return 0


if __name__ == "__main__":
    sys.exit(main("--tous" in sys.argv))
