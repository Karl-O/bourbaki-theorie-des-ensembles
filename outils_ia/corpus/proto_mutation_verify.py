#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Proto generate-and-verify minimal : 1 pas de corruption d'une preuve → filtre noyau.

Premier bout-à-bout du générateur (pivot méta-algo). On prend une preuve VALIDE (une
fonction-théorème), on la CORROMPT d'un cran (supprimer un pas, échanger deux pas
adjacents = le *forward process* de la diffusion), on ré-exécute le programme corrompu,
et on laisse le NOYAU LCF trancher :

  · ERROR : le programme corrompu plante (la corruption casse le code) ;
  · WRONG : il s'exécute mais ne produit PAS le bon théorème (conclusion ≠ cible, ou
            pas un Theoreme) — le noyau/la cible REJETTE ;
  · OK    : il produit ENCORE le bon théorème (le pas corrompu était redondant / l'ordre
            était libre) — corruption « inoffensive ».

Ce que ça démontre :
  1. le **vérificateur exact** (cible + noyau) filtre les corruptions sans bruit ;
  2. on GÉNÈRE ainsi des paires (preuve corrompue → preuve valide) = la donnée
     d'entraînement du *reverse process* (débruitage = réparer la preuve) ;
  3. le taux OK/WRONG/ERROR = la « robustesse » locale d'une preuve = signal de difficulté.

Outillage seulement (outils_ia/) : on exécute des MUTANTS dans une COPIE du namespace du
module ; on ne touche ni `bourbaki/` ni la frontière de confiance. Le noyau reste seul
juge — un Theoreme ne peut toujours être créé que par ses règles.

USAGE : python outils_ia/corpus/proto_mutation_verify.py [module] [theoreme1 theoreme2 ...]
"""
from __future__ import annotations

import ast
import copy
import importlib
import inspect
import sys
import textwrap
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

_DEFAUT_MOD = "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_diagonale_couple"


def _cible_de(mod, name):
    fn = getattr(mod, name + "_cible", None) or getattr(mod, "cible_" + name, None)
    if callable(fn):
        try:
            return fn()
        except Exception:
            return None
    return None


def _instances_de(mod, name):
    """Compagne `<name>_instances()` → [(args, énoncé attendu), …] ou None.

    Contrat du gate PARAMÉTRÉ (7 août 2026) : instances canoniques PETITES,
    énoncés construits par les combinateurs d'énoncé (jamais en re-prouvant).
    La compagne vit dans le module qui DÉFINIT le prouveur — un ré-export ne
    s'exécute pas sous son nom d'alias dans `_statut_parametre`."""
    fn = getattr(mod, name + "_instances", None)
    if not callable(fn):
        return None
    try:
        insts = list(fn())
    except Exception:
        return None
    if insts and all(len(x) == 2 and isinstance(x[0], tuple) for x in insts):
        return insts
    return None


def _rebuild(fdef: ast.FunctionDef, new_body: list) -> str:
    f2 = copy.deepcopy(fdef)
    f2.body = new_body
    mod = ast.Module(body=[f2], type_ignores=[])
    return ast.unparse(ast.fix_missing_locations(mod))


def _mutants(fn_src: str):
    """Engendre les mutants 1-pas : suppression d'un pas, échange de deux pas adjacents."""
    fdef = ast.parse(fn_src).body[0]
    body = fdef.body
    # garder docstring (index 0 si chaîne) et le `return` final hors des suppressions « bêtes »
    start = 1 if (body and isinstance(body[0], ast.Expr)
                  and isinstance(getattr(body[0], "value", None), ast.Constant)) else 0
    for i in range(start, len(body)):
        nb = body[:i] + body[i + 1:]
        if nb:
            yield (f"del#{i}", _rebuild(fdef, nb))
    for i in range(start, len(body) - 1):
        nb = body[:i] + [body[i + 1], body[i]] + body[i + 2:]
        yield (f"swap#{i},{i+1}", _rebuild(fdef, nb))


def evaluer(mod, name: str) -> dict:
    cible = _cible_de(mod, name)
    fn = getattr(mod, name)
    src = textwrap.dedent(inspect.getsource(fn))
    res = {"name": name, "n": 0, "ERROR": 0, "WRONG": 0, "OK": 0, "ok_tags": []}
    for tag, msrc in _mutants(src):
        res["n"] += 1
        ns = dict(mod.__dict__)                       # COPIE du namespace (imports résolus)
        try:
            exec(msrc, ns)
            out = ns[name]()
        except Exception:
            res["ERROR"] += 1
            continue
        if type(out).__name__ == "Theoreme" and cible is not None and out.conclusion == cible:
            res["OK"] += 1
            res["ok_tags"].append(tag)
        else:
            res["WRONG"] += 1
    return res


def main(argv: list[str]) -> int:
    modname = argv[1] if len(argv) > 1 else _DEFAUT_MOD
    mod = importlib.import_module(modname)
    names = argv[2:] or [n for n in getattr(mod, "__all__", [])
                         if not n.endswith("_cible") and callable(getattr(mod, n, None))
                         and _cible_de(mod, n) is not None]
    print(f"# proto generate-and-verify — corruption 1-pas + filtre noyau\n# module {modname}")
    tot = {"n": 0, "ERROR": 0, "WRONG": 0, "OK": 0}
    for name in names:
        try:
            r = evaluer(mod, name)
        except Exception as e:
            print(f"  {name:<32} SKIP ({type(e).__name__})")
            continue
        for k in ("n", "ERROR", "WRONG", "OK"):
            tot[k] += r[k]
        pc = (100 * (r["ERROR"] + r["WRONG"]) // r["n"]) if r["n"] else 0
        print(f"  {name:<32} {r['n']:>3} mutants : {r['ERROR']:>3} ERROR | "
              f"{r['WRONG']:>3} WRONG | {r['OK']:>2} OK   (rejetés {pc}%)")
    if tot["n"]:
        rej = 100 * (tot["ERROR"] + tot["WRONG"]) / tot["n"]
        print(f"\n# TOTAL : {tot['n']} mutants — {tot['ERROR']} ERROR, {tot['WRONG']} WRONG, "
              f"{tot['OK']} OK → le noyau+cible REJETTE {rej:.0f}% des corruptions 1-pas.")
        print("# (chaque rejet = une paire (corrompu→valide) pour entraîner le débruitage ;")
        print("#  chaque OK = un pas redondant/ordre-libre = slack local de la preuve.)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
