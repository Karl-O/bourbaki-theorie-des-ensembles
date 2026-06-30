#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Dataset de paires (preuve corrompue → preuve valide) — forward process (pivot, pas 6).

Construit, à partir des preuves valides, des TRAJECTOIRES DE CORRUPTION progressive :
on part de la preuve valide x0, on applique k corruptions 1-pas successives (suppression
ou échange de pas) → x1, x2, …, xK. Le NOYAU étiquette chaque état (produit-il encore la
cible ?). On émet, par état corrompu, un exemple JSONL :

  { name, n_corruptions:k, statut: OK|WRONG|ERROR,
    valide_src,             # la cible du débruitage (x0)
    corrompu_src,           # l'état bruité (xk)
    parent_src }            # x_{k-1} : la cible d'UN pas de débruitage (diffusion)

→ Donnée d'entraînement du *reverse process* :
   · (corrompu_src → valide_src)  = débruitage complet ;
   · (corrompu_src → parent_src)  = UN pas de débruitage (le bon cadre diffusion/GFlowNet) ;
   · `statut` = récompense dense du noyau (OK = encore valide ; WRONG = autre théorème ;
     ERROR = cassé). La grande majorité des états bruités sont rejetés — c'est le signal.

Outillage seulement (outils_ia/) ; on exécute les mutants dans une COPIE du namespace du
module ; le noyau reste seul juge (aucun Theoreme forgé). Réutilise la machinerie du proto.

USAGE : python outils_ia/corpus/gen_paires_corruption.py [module] [--ntraj N] [--kmax K]
"""
from __future__ import annotations

import importlib
import inspect
import json
import random
import sys
import textwrap
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from proto_mutation_verify import _mutants, _cible_de   # noqa: E402  (machinerie de mutation)

_DEFAUT_MOD = "bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple"


def _statut(mod, name: str, src: str, cible) -> str:
    """OK (cible) | WRONG (autre/aucun théorème) | ERROR (code cassé)."""
    ns = dict(mod.__dict__)
    try:
        exec(src, ns)
        out = ns[name]()
    except Exception:
        return "ERROR"
    if type(out).__name__ == "Theoreme" and cible is not None and out.conclusion == cible:
        return "OK"
    return "WRONG"


def trajectoires(mod, name: str, ntraj: int, kmax: int, rng: random.Random):
    """Engendre des trajectoires de corruption progressive ; yield les exemples-paires."""
    cible = _cible_de(mod, name)
    if cible is None:
        return
    valide = textwrap.dedent(inspect.getsource(getattr(mod, name)))
    for _ in range(ntraj):
        parent, cur = valide, valide
        for k in range(1, kmax + 1):
            muts = list(_mutants(cur))
            if not muts:
                break
            _, cur = rng.choice(muts)             # un cran de corruption de plus
            yield {
                "name": name,
                "n_corruptions": k,
                "statut": _statut(mod, name, cur, cible),
                "valide_src": valide,
                "parent_src": parent,
                "corrompu_src": cur,
            }
            parent = cur


def main(argv: list[str]) -> int:
    args = [a for a in argv[1:] if not a.startswith("--")]
    opts = dict(zip([a for a in argv[1:] if a.startswith("--")],
                    [argv[i + 1] for i, a in enumerate(argv[1:], 1) if a.startswith("--")]))
    modname = args[0] if args else _DEFAUT_MOD
    ntraj = int(opts.get("--ntraj", 3))
    kmax = int(opts.get("--kmax", 4))
    mod = importlib.import_module(modname)
    names = args[1:] or [n for n in getattr(mod, "__all__", [])
                         if not n.endswith("_cible") and callable(getattr(mod, n, None))
                         and _cible_de(mod, n) is not None]
    rng = random.Random(20260630)                  # graine fixe = reproductible
    recs, stat = [], {"OK": 0, "WRONG": 0, "ERROR": 0}
    for name in names:
        for ex in trajectoires(mod, name, ntraj, kmax, rng):
            recs.append(ex)
            stat[ex["statut"]] += 1
    for r in recs:
        print(json.dumps(r, ensure_ascii=False))
    print(f"# {len(recs)} paires ({len(names)} théorèmes, ntraj={ntraj}, kmax={kmax}) — "
          f"statut {stat} ; rejetés {100*(stat['ERROR']+stat['WRONG'])//max(len(recs),1)}%",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
