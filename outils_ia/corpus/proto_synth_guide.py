#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Synthèse GUIDÉE par le prior appris : gain END-TO-END (pivot, pas 20).

Le pas 18 synthétise les termes mais l'énumération brute rate les slots depth-2 (terme-oracle
rang ~561 > budget). Le pas 19 a appris à RANGER les candidats (rang 396→140). Ici on BRANCHE
le prior dans la synthèse : on range le pool de candidats par P(correct) AVANT le filtre noyau,
à BUDGET FIXE (CAP essais-noyau/bloc), et on mesure le taux de régénération de bloc — BRUTE
(ordre d'énumération) vs PRIOR (ordre du modèle) — sur des preuves TENUES À L'ÉCART (identite,
depth-2, où le brut donnait 0 %). Le prior trained sur des modules d'ENTRAÎNEMENT distincts.

generate(politique-prior) + verify(noyau) : le noyau reste seul juge à l'exécution ; le prior
ne fait que prioriser l'ordre d'essai. Outillage seulement (outils_ia/) ; aucun Theoreme forgé.
USAGE : python outils_ia/corpus/proto_synth_guide.py
"""
from __future__ import annotations

import ast
import copy
import itertools
import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

import numpy as np                                          # noqa: E402
from sklearn.feature_extraction import DictVectorizer       # noqa: E402
from sklearn.linear_model import LogisticRegression         # noqa: E402

import proto_synth_termes as PST                            # noqa: E402
from proto_synth_termes import synth_termes, _slots         # noqa: E402
from proto_synth_prior import collecte, _feats, _head        # noqa: E402
from proto_macro_noyau import _proofs, _occurrences, NS      # noqa: E402
from proto_macro_termes import _str_consts, _ctx_trou        # noqa: E402
from proto_mutation_verify import _cible_de, _rebuild        # noqa: E402
from gen_paires_corruption import _statut                    # noqa: E402
from repair_learned import _assignes                         # noqa: E402

PST.MAXT = 2000          # pool large (le terme-oracle depth-2 ~rang 561 doit y être)
CAP = 200                # budget FIXE d'essais-noyau par bloc
TRAIN = [
    "bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projection_fonctionnelle",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_diagonale_couple",
]
TEST = ["bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_identite_neutre"]   # depth-2, tenu à l'écart


def _ranke_slot(pool, cf, k, manq, disp, outs, model, vec):
    sc = model.predict_proba(vec.transform([_feats(t, cf, k, manq, disp, outs) for t in pool]))[:, 1]
    return [pool[i] for i in np.argsort(-sc)]


def regen_guide(mod, P, infoP, occ, L, pool, vars_locales, model, vec, use_prior):
    """Régénère le bloc [occ,occ+L) de P par synthèse ; range le pool par prior si use_prior. Noyau OK ?"""
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
        ordres.append(_ranke_slot(pool, cf, k, manq, disp, outs, model, vec) if use_prior else list(pool))
    if len(slots) == 1:
        grids = ((c,) for c in ordres[0][:CAP])
    else:
        T = 32
        ij = [(i, j) for i in range(min(T, len(ordres[0]))) for j in range(min(T, len(ordres[1])))]
        ij.sort(key=lambda p: p[0] + p[1])                  # rang combiné croissant
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


def main(argv):
    print("# entraînement du prior (LogReg) sur modules d'ENTRAÎNEMENT…", file=sys.stderr)
    X, y, groups, slot_ids, brut = collecte(TRAIN)
    vec = DictVectorizer(sparse=False)
    Xv = vec.fit_transform(X)
    model = LogisticRegression(max_iter=2000, class_weight="balanced").fit(Xv, y)
    print(f"# prior entraîné : {len(y)} exemples ({y.sum()} +) | test synthèse sur preuves TENUES À L'ÉCART")

    tot = {"blocs": 0, "in_gram": 0, "brute": 0, "prior": 0, "slots": 0, "slots_in": 0}
    rbrut, rprior = [], []
    for modname in TEST:
        mod, proofs = _proofs(modname)
        if not proofs:
            continue
        vars_locales = {v for _, b, s, _ in proofs.values() for st in b[s:] for v in _assignes(st)}
        from collections import defaultdict
        ng = defaultdict(set)
        for nm, (_, _, _, sg) in proofs.items():
            for nl in NS:
                for i in range(len(sg) - nl + 1):
                    ng[tuple(sg[i:i + nl])].add(nm)
        macros = {m for m, pr in ng.items() if len(pr) >= 2}
        for P in proofs:
            fdef, body, start, sigs = proofs[P]
            params = {a.arg for a in fdef.args.args}
            var_atoms = {v for st in body[start:] for v in _assignes(st)} | params
            str_atoms = {s for s in _str_consts(body) if s.isidentifier() and len(s) <= 3}
            pool = synth_termes(var_atoms, str_atoms)
            pd = [ast.dump(t) for t in pool]
            seen = set()
            for macro in macros:
                for occ in _occurrences(sigs, macro):
                    key = (P, occ, len(macro))
                    if key in seen:
                        continue
                    seen.add(key)
                    L = len(macro)
                    block = body[start + occ:start + occ + L]
                    manq, disp, _ = _ctx_trou(proofs[P], occ, L, vars_locales)
                    outs = {v for st in block for v in _assignes(st)}
                    # slots + couverture grammaire + rang brut/prior par slot in-grammaire
                    slots, in_gram = [], True
                    for st in block:
                        call = next((n for n in ast.walk(st) if isinstance(n, ast.Call)), None)
                        if call is None:
                            continue
                        for k in _slots(call):
                            slots.append(1)
                            tot["slots"] += 1
                            od = ast.dump(call.args[k])
                            if od in pd:
                                tot["slots_in"] += 1
                                bi = pd.index(od)
                                sc = model.predict_proba(vec.transform(
                                    [_feats(t, _head(call), k, manq, disp, outs) for t in pool]))[:, 1]
                                pr = list(np.argsort(-sc)).index(bi)
                                rbrut.append(bi + 1)
                                rprior.append(pr + 1)
                            else:
                                in_gram = False                # slot hors grammaire → bloc insynthétisable
                    if not slots or len(slots) > 2:
                        continue
                    tot["blocs"] += 1
                    if not in_gram:
                        continue
                    tot["in_gram"] += 1
                    tot["brute"] += int(bool(regen_guide(mod, P, proofs[P], occ, L, pool,
                                                          vars_locales, model, vec, False)))
                    tot["prior"] += int(bool(regen_guide(mod, P, proofs[P], occ, L, pool,
                                                         vars_locales, model, vec, True)))
    print(f"\n# pas 20 — synthèse GUIDÉE à budget FIXE (CAP={CAP}) sur preuves TENUES À L'ÉCART (depth-2) :")
    print(f"# couverture grammaire : {tot['slots_in']}/{tot['slots']} slots dans la grammaire de termes "
          f"(le reste = constructeurs non couverts : conjonction_intro, helpers…).")
    if rbrut:
        print(f"# rang du bon terme (slots in-grammaire) : brut {np.mean(rbrut):.0f} → prior "
              f"{np.mean(rprior):.0f} (le prior shallow bouge à peine les termes depth-2).")
    ig = tot["in_gram"]
    if ig:
        print(f"# régénération end-to-end ({ig} blocs FULLY in-grammaire) : BRUTE {tot['brute']} "
              f"({100*tot['brute']//ig}%) → PRIOR {tot['prior']} ({100*tot['prior']//ig}%).")
    else:
        print(f"# 0 bloc FULLY in-grammaire parmi {tot['blocs']} (chaque bloc a ≥1 slot hors grammaire).")
    print("# RÉSULTAT NÉGATIF À DOUBLE CAUSE : (1) grammaire de termes trop étroite (manque des")
    print("# constructeurs/lemmes) ; (2) le prior SHALLOW ne range pas les termes depth-2 sous le budget")
    print("# (rang ~500, à peine bougé). → pas 21 : grammaire enrichie + modèle STRUCTURÉ (embeddings AST).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
