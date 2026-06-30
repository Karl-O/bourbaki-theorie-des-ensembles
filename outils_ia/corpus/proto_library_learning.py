#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Library-learning : miner les MACROS multi-pas récurrentes inter-preuves (pivot, pas 16).

Le pas 14 a montré qu'un pas ISOLÉ d'une autre preuve ne transfère pas (verbatim ~0 %, import
d'une tactique étrangère 0 %) : chaque preuve se suffit en tactiques. Le levier inter-preuves
n'est donc pas le pas isolé, mais le **bloc MULTI-pas récurrent** — une *macro* = une
sous-séquence contiguë de tactiques *(fn, arité)* qui RÉAPPARAÎT dans plusieurs preuves. Une
macro porte son propre flot-de-données interne, donc peut être un vrai morceau de vocabulaire
PARTAGÉ (≠ le 1-pas du pas 14).

Cet outil (analyse AST PURE, aucun exec-noyau → rapide et large) :
  1. représente chaque preuve comme la SUITE de ses signatures de tactiques ;
  2. mine les n-grammes contigus (n=2..4) et garde ceux qui apparaissent dans ≥2 preuves
     (« macro inter-preuves ») — distingue le partage INTRA-module et INTER-modules ;
  3. mesure la COMPRESSION : en couvrant chaque preuve par les macros (greedy, plus longue
     d'abord, non-chevauchant), combien de pas sont absorbés, et de combien la preuve raccourcit
     si chaque macro compte pour 1 « appel ». Une petite bibliothèque qui couvre beaucoup = le
     vocabulaire multi-pas partagé existe (à valider ensuite par le noyau, pas 16-suite).

Outillage seulement (outils_ia/) ; ne fabrique aucun Theoreme ; ne touche pas la frontière.
USAGE : python outils_ia/corpus/proto_library_learning.py [package1 package2 ...]
"""
from __future__ import annotations

import ast
import importlib
import inspect
import sys
import textwrap
from collections import defaultdict
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

from export_corpus import _decouvrir                     # noqa: E402  (découverte de modules)
from repair_learned import _fn_principale, _n_args       # noqa: E402

PACKAGES = ["bourbaki.logique", "bourbaki.ensembles"]    # rapides (PAS cardinaux/entiers)
NS = (2, 3, 4)                                            # longueurs de macro minées


def _preuves(modname):
    """(id_preuve, suite de signatures (fn,arité)) pour chaque fonction-théorème du module."""
    try:
        mod = importlib.import_module(modname)
    except Exception:
        return []
    court = modname.split(".")[-1]
    out = []
    for name in getattr(mod, "__all__", []):
        if name.endswith("_cible"):
            continue
        fn = getattr(mod, name, None)
        if not callable(fn):
            continue
        try:
            fdef = ast.parse(textwrap.dedent(inspect.getsource(fn))).body[0]
        except Exception:
            continue
        if not isinstance(fdef, ast.FunctionDef):
            continue
        body = fdef.body
        start = 1 if (body and isinstance(body[0], ast.Expr)
                      and isinstance(getattr(body[0], "value", None), ast.Constant)) else 0
        sigs = [(_fn_principale(s), _n_args(s)) for s in body[start:]]
        if len(sigs) >= 2:
            out.append((f"{court}.{name}", court, sigs))
    return out


def miner(preuves):
    """n-grammes contigus → {ngram: (nb preuves distinctes, nb modules distincts, occurrences)}."""
    ng_preuves = defaultdict(set)
    ng_modules = defaultdict(set)
    ng_occ = defaultdict(int)
    for pid, mod, sigs in preuves:
        for n in NS:
            for i in range(len(sigs) - n + 1):
                ng = tuple(sigs[i:i + n])
                ng_preuves[ng].add(pid)
                ng_modules[ng].add(mod)
                ng_occ[ng] += 1
    return {ng: (len(ng_preuves[ng]), len(ng_modules[ng]), ng_occ[ng])
            for ng in ng_preuves}


def couvrir(sigs, macros_par_len):
    """Greedy non-chevauchant, plus longue macro d'abord : (pas couverts, nb d'instances)."""
    i, couverts, instances, n = 0, 0, 0, len(sigs)
    while i < n:
        pris = False
        for L in sorted(NS, reverse=True):
            if i + L <= n and tuple(sigs[i:i + L]) in macros_par_len[L]:
                couverts += L
                instances += 1
                i += L
                pris = True
                break
        if not pris:
            i += 1
    return couverts, instances


def _fmt_macro(ng):
    return " → ".join(f"{fn}/{a}" for fn, a in ng)


def main(argv):
    packages = argv[1:] or PACKAGES
    modules = _decouvrir(packages)
    print(f"# library-learning : {len(modules)} modules sous {packages}", file=sys.stderr)
    preuves = []
    for m in modules:
        preuves.extend(_preuves(m))
    pas_tot = sum(len(s) for _, _, s in preuves)
    print(f"# corpus : {len(preuves)} preuves (≥2 pas), {pas_tot} pas de tactique au total")

    macros_all = miner(preuves)
    # macro INTER-preuves = apparaît dans ≥2 preuves distinctes
    macros = {ng: v for ng, v in macros_all.items() if v[0] >= 2}
    inter_mod = {ng: v for ng, v in macros.items() if v[1] >= 2}
    print(f"# n-grammes distincts {len(macros_all)} | macros INTER-preuves (≥2 preuves) {len(macros)} "
          f"| dont INTER-modules (≥2 modules) {len(inter_mod)}")

    par_len = {L: {ng for ng in macros if len(ng) == L} for L in NS}
    for L in NS:
        print(f"#   longueur {L} : {len(par_len[L])} macros inter-preuves")

    # COMPRESSION par la bibliothèque (toutes les macros inter-preuves)
    tot_couv = tot_inst = 0
    for _, _, sigs in preuves:
        c, inst = couvrir(sigs, par_len)
        tot_couv += c
        tot_inst += inst
    comprime = (pas_tot - tot_couv) + tot_inst             # pas libres + 1 par instance de macro
    print(f"\n[compression] {tot_couv}/{pas_tot} pas absorbés par une macro "
          f"({100*tot_couv//max(pas_tot,1)}%), {tot_inst} instances ; longueur compressée "
          f"{comprime} vs {pas_tot} → ratio {comprime/max(pas_tot,1):.2f} "
          f"(une preuve = pas-libres + appels-macro).")

    # bibliothèque RÉDUITE : top-K macros par (nb preuves, longueur) ; couverture obtenue
    classement = sorted(macros.items(), key=lambda kv: (-kv[1][0], -len(kv[0]), -kv[1][2]))
    for K in (10, 25, 50):
        topK = classement[:K]
        par_len_K = {L: {ng for ng, _ in topK if len(ng) == L} for L in NS}
        couvK = sum(couvrir(s, par_len_K)[0] for _, _, s in preuves)
        print(f"[bib. top-{K:>2}] couvre {couvK}/{pas_tot} pas ({100*couvK//max(pas_tot,1)}%)")

    print("\n# top macros inter-preuves (tactique/arité) — vocabulaire multi-pas PARTAGÉ :")
    for ng, (npr, nmod, occ) in classement[:12]:
        print(f"    [{npr:>2} preuves / {nmod} mod / {occ:>3} occ] {_fmt_macro(ng)}")
    print("# = candidat-vocabulaire pour générer/vérifier des BLOCS multi-pas (noyau validant, pas 16-suite).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
