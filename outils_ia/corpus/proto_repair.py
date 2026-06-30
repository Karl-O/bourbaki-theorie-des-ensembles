#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Proto REVERSE process : repaireur d'un pas (1er débruitage) — pivot méta-algo, pas 7.

Le pas 5 a montré le *forward* (corrompre + filtre noyau). Voici le *reverse* atomique :
étant donné une preuve corrompue par SUPPRESSION d'un pas, RÉPARER = chercher quelle
brique, ré-insérée à l'emplacement manquant, fait re-produire la cible — le NOYAU étant
le juge exact de l'acceptation. C'est UN pas de débruitage (diffusion / GFlowNet) :

    état bruité  ──(chercher dans la bibliothèque + filtre noyau)──▶  état réparé valide

Repaireur TRIVIAL (brute-force, pas encore appris) : la « bibliothèque » candidate = les
pas du corpus local (ici les statements de la preuve elle-même = un minimum viable). On
ré-insère chaque candidat à l'emplacement supprimé et on garde ceux que le noyau ACCEPTE
(conclusion == cible). Ce que ça démontre :
  · RÉCUPÉRABILITÉ : l'oracle (le pas d'origine) est toujours accepté → la preuve est
    réparable par recherche+vérification ;
  · STRICTESSE DU FILTRE : presque aucun autre candidat ne passe (le noyau rejette) ;
  · SLACK : quand un candidat ≠ oracle passe aussi, la preuve a une réparation alternative.

Outillage seulement (outils_ia/) ; mutants exécutés dans une COPIE du namespace ; le noyau
reste seul juge (aucun Theoreme forgé). Réutilise la machinerie des protos précédents.

USAGE : python outils_ia/corpus/proto_repair.py [module] [theoreme1 ...]
"""
from __future__ import annotations

import ast
import importlib
import inspect
import sys
import textwrap
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from proto_mutation_verify import _cible_de, _rebuild   # noqa: E402
from gen_paires_corruption import _statut               # noqa: E402

_DEFAUT_MOD = "bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple"


def reparer(mod, name: str) -> dict:
    """Pour chaque suppression 1-pas, cherche les réparations acceptées par le noyau."""
    cible = _cible_de(mod, name)
    fdef = ast.parse(textwrap.dedent(inspect.getsource(getattr(mod, name)))).body[0]
    body = fdef.body
    start = 1 if (body and isinstance(body[0], ast.Expr)
                  and isinstance(getattr(body[0], "value", None), ast.Constant)) else 0
    pool = body[start:]                                  # bibliothèque candidate (pas locaux)
    res = {"name": name, "deletions": 0, "recouvrables": 0, "alt_repairs": 0, "essais": 0}
    for i in range(start, len(body)):
        deleted = body[i]
        corrompu = body[:i] + body[i + 1:]              # preuve avec le pas i supprimé
        oracle_dump = ast.dump(deleted)
        accepted_alt = oracle_ok = False
        for cand in pool:                               # chercher un candidat qui répare
            essai = corrompu[:i] + [cand] + corrompu[i:]
            res["essais"] += 1
            if _statut(mod, name, _rebuild(fdef, essai), cible) == "OK":
                if ast.dump(cand) == oracle_dump:
                    oracle_ok = True
                else:
                    accepted_alt = True
        res["deletions"] += 1
        res["recouvrables"] += int(oracle_ok)
        res["alt_repairs"] += int(accepted_alt)
    return res


def main(argv: list[str]) -> int:
    modname = argv[1] if len(argv) > 1 else _DEFAUT_MOD
    mod = importlib.import_module(modname)
    names = argv[2:] or [n for n in getattr(mod, "__all__", [])
                         if not n.endswith("_cible") and callable(getattr(mod, n, None))
                         and _cible_de(mod, n) is not None]
    print(f"# proto REVERSE — repaireur 1-pas (search bibliothèque + filtre noyau)\n# {modname}")
    tot = {"deletions": 0, "recouvrables": 0, "alt_repairs": 0, "essais": 0}
    for name in names:
        try:
            r = reparer(mod, name)
        except Exception as e:
            print(f"  {name:<32} SKIP ({type(e).__name__})")
            continue
        for k in tot:
            tot[k] += r[k]
        print(f"  {name:<32} {r['deletions']:>2} suppressions : "
              f"{r['recouvrables']:>2} récupérées (oracle) | {r['alt_repairs']:>2} avec répar. alternative "
              f"| {r['essais']} essais")
    if tot["deletions"]:
        print(f"\n# TOTAL : {tot['deletions']} corruptions réparables — "
              f"{tot['recouvrables']} récupérées par recherche+noyau "
              f"({100*tot['recouvrables']//tot['deletions']}%), "
              f"{tot['alt_repairs']} avec réparation ALTERNATIVE (slack), {tot['essais']} essais filtrés.")
        print("# = 1 pas de débruitage démontré : chercher dans la bibliothèque, le noyau valide.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
