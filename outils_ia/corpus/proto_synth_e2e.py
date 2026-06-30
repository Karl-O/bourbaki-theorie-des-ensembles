#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""SYNTHÈSE END-TO-END guidée par le TreeNN, NOYAU validant (pivot, pas 27 = LE but).

Aboutissement de l'arc pas 18→26 : on ne mesure plus seulement le RANG du bon terme (pas 21-26),
on REGÉNÈRE réellement des blocs-macro tenus à l'écart en synthétisant leurs slots-termes et en
laissant le NOYAU juger (generate-and-verify). Le ranker n'est plus le LogReg shallow (pas 20, qui
plafonnait → 0 %) mais le **TreeNN structuré** (proto_synth_torch : médiane 1 / top-5 69 %), entraîné
sur des modules d'ENTRAÎNEMENT distincts, avec la grammaire ENRICHIE (pas 23-26, couverture 64 %).

Protocole : pour chaque bloc tenu à l'écart, on range le pool de candidats par score TreeNN (ordre
BRUT = énumération en comparaison), puis on essaie les mieux classés à BUDGET FIXE (CAP essais-noyau)
jusqu'à ce que `_statut(...) == "OK"`. Taux de régénération BRUT vs TreeNN = le gain end-to-end réel.

Le noyau reste SEUL juge à l'exécution ; le TreeNN ne fait que prioriser l'ordre d'essai. Outillage
seulement (outils_ia/) ; aucun Theoreme forgé. USAGE : python outils_ia/corpus/proto_synth_e2e.py
"""
from __future__ import annotations

import ast
import copy
import sys
from collections import defaultdict
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

import numpy as np                                              # noqa: E402

import proto_synth_termes as PST                               # noqa: E402
from proto_synth_termes import synth_termes, _slots            # noqa: E402
from proto_synth_torch import collecte_slots, _entraine, _scores_ens, CF_VOCAB  # noqa: E402
from proto_synth_prior import _head                            # noqa: E402
from proto_macro_noyau import _proofs, _occurrences, TEST_LOURD, NS  # noqa: E402
from proto_macro_termes import _str_consts, _ctx_trou          # noqa: E402
from proto_mutation_verify import _cible_de, _rebuild          # noqa: E402
from gen_paires_corruption import _statut                      # noqa: E402
from repair_learned import _assignes                           # noqa: E402

PST.MAXT = 1500          # pool objets ≤1500 (+ formes ≤1500) ; le terme-oracle depth-2 doit y être
CAP = 200                # budget FIXE d'essais-noyau par bloc
E = 2                    # ensemble de graines
HOLDOUT = "module"       # "module" (pas 27 : module test jamais vu → TreeNN 50 %) | "proof" (pas 28 :
#                          leave-one-out — sur les 2 preuves MIROIR d'identite, 0 % car la sœur tenue
#                          DANS le train est ADVERSARIALE : même contexte, arrangement opposé. cf README.
TRAIN = [                # modules d'ENTRAÎNEMENT (distincts du test)
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_projection_fonctionnelle",
    "bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple",
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_produit_extensionnalite",
]
TEST = ["bourbaki.ensembles.ii_3_correspondances.ensembles_identite_neutre"]   # depth-2, tenu à l'écart


def _ordre(pool, nets, cf, k, manq, disp, outs, use_tree):
    """Indices du pool ordonnés best-first : score TreeNN si use_tree, sinon énumération."""
    if not use_tree:
        return list(range(len(pool)))
    s = {"pool": pool, "cf": cf, "pos": k, "manq": manq, "disp": disp, "outs": outs}
    sc = _scores_ens(nets, s)
    return list(np.argsort(-sc))


def regen_e2e(mod, P, infoP, occ, L, pool, vars_locales, nets, use_tree):
    """Régénère le bloc [occ,occ+L) par synthèse, pool rangé par TreeNN, noyau OK à budget CAP ?"""
    fdef, body, start = infoP[0], infoP[1], infoP[2]
    cible = _cible_de(mod, P)
    absj = start + occ
    block = body[absj:absj + L]
    manq, disp, _ = _ctx_trou(infoP, occ, L, vars_locales)
    outs = {v for st in block for v in _assignes(st)}
    slots = []
    for st in block:
        call = next((n for n in ast.walk(st) if isinstance(n, ast.Call)), None)
        if call is None:
            continue
        for k in _slots(call):
            slots.append((_head(call), k))
    if not slots or len(slots) > 2:
        return None
    ordres = []
    for (cf, k) in slots:
        idx = _ordre(pool, nets, cf, k, manq, disp, outs, use_tree)
        ordres.append([pool[i] for i in idx])
    if len(slots) == 1:
        grids = ((c,) for c in ordres[0][:CAP])
    else:
        T = 32
        ij = [(i, j) for i in range(min(T, len(ordres[0]))) for j in range(min(T, len(ordres[1])))]
        ij.sort(key=lambda p: p[0] + p[1])                     # rang combiné croissant
        grids = ((ordres[0][i], ordres[1][j]) for i, j in ij[:CAP])
    n = 0
    for grid in grids:
        newblock = []
        gi = 0
        for st in block:
            ns = copy.deepcopy(st)
            call = next((nn for nn in ast.walk(ns) if isinstance(nn, ast.Call)), None)
            if call is not None:
                for k in _slots(call):
                    call.args[k] = copy.deepcopy(grid[gi])
                    gi += 1
            ast.fix_missing_locations(ns)
            newblock.append(ns)
        recon = body[:absj] + newblock + body[absj + L:]
        n += 1
        if _statut(mod, P, _rebuild(fdef, recon), cible) == "OK":
            return True
        if n >= CAP:
            break
    return False


def collecte_named(modnames, exclude=None):
    """Comme proto_synth_torch.collecte_slots mais TAGGE le nom de la preuve et peut en EXCLURE une
    (leave-one-out proof-level). Remplit CF_VOCAB. Réutilise la même logique de slots in-grammaire."""
    slots = []
    gid = 0
    for modname in modnames:
        mod, proofs = _proofs(modname)
        if not proofs:
            continue
        vl = {v for _, b, s, _ in proofs.values() for st in b[s:] for v in _assignes(st)}
        ng = defaultdict(set)
        for nm, (_, _, _, sg) in proofs.items():
            for nl in NS:
                for i in range(len(sg) - nl + 1):
                    ng[tuple(sg[i:i + nl])].add(nm)
        macros = {m for m, pr in ng.items() if len(pr) >= 2}
        for P in proofs:
            if P in TEST_LOURD or P == exclude:
                continue
            gid += 1
            fdef, body, start, sigs = proofs[P]
            params = {a.arg for a in fdef.args.args}
            va = {v for st in body[start:] for v in _assignes(st)} | params
            sa = {s for s in _str_consts(body) if s.isidentifier() and len(s) <= 3}
            pool = synth_termes(va, sa)
            pd = [ast.dump(t) for t in pool]
            seen = set()
            for macro in macros:
                for occ in _occurrences(sigs, macro):
                    if (occ, len(macro)) in seen:
                        continue
                    seen.add((occ, len(macro)))
                    L = len(macro)
                    block = body[start + occ:start + occ + L]
                    manq, disp, _ = _ctx_trou(proofs[P], occ, L, vl)
                    outs = {v for st in block for v in _assignes(st)}
                    for st in block:
                        call = next((n for n in ast.walk(st) if isinstance(n, ast.Call)), None)
                        if call is None:
                            continue
                        cf = _head(call)
                        for k in _slots(call):
                            od = ast.dump(call.args[k])
                            if od not in pd:
                                continue
                            CF_VOCAB.setdefault(cf, len(CF_VOCAB) + 1)
                            slots.append({"cf": cf, "pos": k, "manq": manq, "disp": disp,
                                          "outs": outs, "pool": pool, "pos_idx": pd.index(od),
                                          "group": gid, "proof": P})
    return slots


def _eval_proof(modname, P, nets, tot):
    """Évalue tous les blocs in-grammaire (≤2 slots) de la preuve P avec les nets fournis."""
    mod, proofs = _proofs(modname)
    vl = {v for _, b, s, _ in proofs.values() for st in b[s:] for v in _assignes(st)}
    ng = defaultdict(set)
    for nm, (_, _, _, sg) in proofs.items():
        for nl in NS:
            for i in range(len(sg) - nl + 1):
                ng[tuple(sg[i:i + nl])].add(nm)
    macros = {m for m, pr in ng.items() if len(pr) >= 2}
    fdef, body, start, sigs = proofs[P]
    params = {a.arg for a in fdef.args.args}
    va = {v for st in body[start:] for v in _assignes(st)} | params
    sa = {s for s in _str_consts(body) if s.isidentifier() and len(s) <= 3}
    pool = synth_termes(va, sa)
    pd = set(ast.dump(t) for t in pool)
    seen = set()
    for macro in macros:
        for occ in _occurrences(sigs, macro):
            key = (P, occ, len(macro))
            if key in seen:
                continue
            seen.add(key)
            L = len(macro)
            block = body[start + occ:start + occ + L]
            slots, in_gram = [], True
            for st in block:
                call = next((n for n in ast.walk(st) if isinstance(n, ast.Call)), None)
                if call is None:
                    continue
                for k in _slots(call):
                    slots.append(1)
                    if ast.dump(call.args[k]) not in pd:
                        in_gram = False
            if not slots or len(slots) > 2:
                continue
            tot["blocs"] += 1
            if not in_gram:
                continue
            tot["in_gram"] += 1
            manq, disp, _ = _ctx_trou(proofs[P], occ, L, vl)
            outs = {v for st in block for v in _assignes(st)}
            rangs = []
            for st in block:
                call = next((n for n in ast.walk(st) if isinstance(n, ast.Call)), None)
                if call is None:
                    continue
                for k in _slots(call):
                    od = ast.dump(call.args[k])
                    bi = [ast.dump(t) for t in pool].index(od)
                    order = _ordre(pool, nets, _head(call), k, manq, disp, outs, True)
                    rangs.append((bi + 1, order.index(bi) + 1))
            tot["brut"] += int(bool(regen_e2e(mod, P, proofs[P], occ, L, pool, vl, nets, False)))
            tot["tree"] += int(bool(regen_e2e(mod, P, proofs[P], occ, L, pool, vl, nets, True)))
            print(f"#   [{HOLDOUT}] bloc {P}@{occ} (L={L}) rangs(brut,tree)={rangs} : "
                  f"brut={tot['brut']} tree={tot['tree']} / in_gram={tot['in_gram']}", file=sys.stderr)


def main(argv):
    tot = {"blocs": 0, "in_gram": 0, "brut": 0, "tree": 0}
    if HOLDOUT == "module":
        print(f"# [module] entraînement TreeNN sur {len(TRAIN)} modules (test JAMAIS vu)…", file=sys.stderr)
        nets = [_entraine(collecte_named(TRAIN), seed=sd) for sd in range(E)]
        for modname in TEST:
            _, proofs = _proofs(modname)
            for P in proofs:
                if P not in TEST_LOURD:
                    _eval_proof(modname, P, nets, tot)
    else:  # proof-level : pour CHAQUE preuve test, ré-entraîner en l'EXCLUANT (module vu via les sœurs)
        allmods = TRAIN + TEST
        for modname in TEST:
            _, proofs = _proofs(modname)
            for P in proofs:
                if P in TEST_LOURD:
                    continue
                print(f"# [proof] ré-entraînement TreeNN en excluant {P}…", file=sys.stderr)
                nets = [_entraine(collecte_named(allmods, exclude=P), seed=sd) for sd in range(E)]
                _eval_proof(modname, P, nets, tot)
    print(f"\n# pas 28 — RÉGÉNÉRATION END-TO-END (holdout={HOLDOUT}, CAP={CAP}, noyau validant) :")
    ig = tot["in_gram"]
    print(f"# {tot['blocs']} blocs (≤2 slots) ; {ig} FULLY in-grammaire (grammaire enrichie pas 23-26).")
    if ig:
        print(f"# régénérés : BRUT {tot['brut']} ({100*tot['brut']//ig}%) → TreeNN {tot['tree']} "
              f"({100*tot['tree']//ig}%).")
        if tot["tree"] > tot["brut"]:
            print("# → le TreeNN FRANCHIT le budget là où l'énumération brute échoue = generate-and-verify")
            print("#   appris end-to-end (1re régénération depth-2 réelle guidée par le modèle structuré).")
        elif tot["tree"] == tot["brut"] and tot["tree"] > 0:
            print("# → BRUT et TreeNN régénèrent autant ici (slots faciles / CAP large) ; voir détail rangs.")
    else:
        print("# 0 bloc FULLY in-grammaire — augmenter la grammaire / le pool.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
