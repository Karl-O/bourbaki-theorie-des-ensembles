#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""PRIOR APPRIS qui RANGE les termes candidats de la synthèse (pivot, pas 19).

Le pas 18 a montré que la synthèse GÉNÈRE les bons termes, mais que l'énumération brute les
classe trop loin (terme-oracle depth-2 au rang ~561/7265). Ici on APPREND à ranger : pour
chaque slot-terme, on génère le pool de candidats (synth_termes) et on entraîne un classifieur
sklearn à prédire « ce candidat est-il le terme attendu ? » depuis des features de CONTEXTE
(tactique appelante + position d'argument ; profondeur/forme du terme candidat ; data-flow : le
terme utilise-t-il les variables locales/manquantes pertinentes). On range alors par P(correct)
et on mesure le RANG du bon terme — modèle vs énumération brute.

Astuce clé : l'oracle de label est GRATUIT (égalité au terme réel de P au même slot), donc AUCUN
appel-noyau pour l'entraînement. Le noyau reste le juge à l'EXÉCUTION (pas 20) ; ici on apprend
juste le prior. GroupKFold par PREUVE → test sur des preuves jamais vues (aucune fuite).

Outillage seulement (outils_ia/) ; ne fabrique aucun Theoreme. Réutilise proto_synth_termes.
USAGE : python outils_ia/corpus/proto_synth_prior.py [module1 module2 ...]
"""
from __future__ import annotations

import ast
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
from sklearn.ensemble import RandomForestClassifier         # noqa: E402
from sklearn.model_selection import GroupKFold              # noqa: E402

import proto_synth_termes as PST                            # noqa: E402
from proto_synth_termes import synth_termes, _slots         # noqa: E402
from proto_macro_noyau import _proofs, _occurrences, TEST_LOURD, NS  # noqa: E402
from proto_macro_termes import _str_consts, _ctx_trou       # noqa: E402
from repair_learned import _assignes                        # noqa: E402

PST.MAXT = 2500          # gros pool (sans noyau : featurisation seule) pour inclure les termes depth-2
MODULES = [
    "bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projection_fonctionnelle",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_identite_neutre",
    "bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_diagonale_couple",
]


def _depth(t):
    if isinstance(t, (ast.Name, ast.Constant)):
        return 0
    if isinstance(t, ast.Call):
        return 1 + max((_depth(a) for a in t.args), default=0)
    return 0


def _head(t):
    if isinstance(t, ast.Name):
        return "atome"
    if isinstance(t, ast.Constant):
        return "const"
    if isinstance(t, ast.Call):
        f = t.func
        if isinstance(f, ast.Attribute):
            return f.attr
        if isinstance(f, ast.Name):
            return f.id
    return "?"


def _leaves(t):
    noms, strs = set(), set()
    for n in ast.walk(t):
        if isinstance(n, ast.Name):
            noms.add(n.id)
        elif isinstance(n, ast.Constant) and isinstance(n.value, str):
            strs.add(n.value)
    return noms, strs


def _feats(t, cf, pos, manq, disp, outs):
    noms, strs = _leaves(t)
    nnodes = sum(1 for _ in ast.walk(t))
    return {
        "cf": cf, "pos": pos,
        "depth": _depth(t), "head": _head(t),
        "nnodes": nnodes, "natoms": len(noms),
        "df_manq": len(noms & manq),            # data-flow : leaves ∈ variables manquantes (sorties)
        "df_disp": len(noms & disp),            # leaves ∈ variables disponibles (pré-trou)
        "df_outs": len(noms & outs),            # leaves ∈ variables assignées par le bloc
        "has_varstr": int(any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                              and n.func.id == "var" for n in ast.walk(t))),
    }


def collecte(modnames):
    """Pour chaque slot-terme : (features par candidat, label=égalité oracle, groupe=preuve, rang brut)."""
    X, y, groups, slot_ids, brut = [], [], [], [], {}
    gid = 0
    sid = 0
    for modname in modnames:
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
            if P in TEST_LOURD:
                continue
            gid += 1
            fdef, body, start, sigs = proofs[P]
            params = {a.arg for a in fdef.args.args}
            var_atoms = {v for st in body[start:] for v in _assignes(st)} | params
            str_atoms = {s for s in _str_consts(body) if s.isidentifier() and len(s) <= 3}
            pool = synth_termes(var_atoms, str_atoms)
            pool_dumps = [ast.dump(t) for t in pool]
            for macro in macros:
                for occ in _occurrences(sigs, macro):
                    L = len(macro)
                    manq, disp, absj = _ctx_trou(proofs[P], occ, L, vars_locales)
                    outs = {v for st in body[start + occ:start + occ + L] for v in _assignes(st)}
                    for st in body[start + occ:start + occ + L]:
                        call = next((n for n in ast.walk(st) if isinstance(n, ast.Call)), None)
                        if call is None:
                            continue
                        cf = _head(call)
                        for k in _slots(call):
                            oracle = call.args[k]
                            od = ast.dump(oracle)
                            if od not in pool_dumps:
                                continue                   # terme-oracle hors grammaire/pool : slot ignoré
                            sid += 1
                            brut[sid] = pool_dumps.index(od) + 1   # rang brut (énumération)
                            for t, td in zip(pool, pool_dumps):
                                X.append(_feats(t, cf, k, manq, disp, outs))
                                y.append(int(td == od))
                                groups.append(gid)
                                slot_ids.append(sid)
    return X, np.array(y), np.array(groups), np.array(slot_ids), brut


def main(argv):
    modnames = argv[1:] or MODULES
    print(f"# collecte sur {len(modnames)} modules (label = égalité au terme réel de P, sans noyau)…",
          file=sys.stderr)
    X, y, groups, slot_ids, brut = collecte(modnames)
    if len(X) == 0 or y.sum() == 0:
        print("# pas de slots in-grammaire", file=sys.stderr)
        return 1
    vec = DictVectorizer(sparse=False)
    Xv = vec.fit_transform(X)
    nslots = len(set(slot_ids))
    print(f"# {len(y)} candidat-features | {nslots} slots in-grammaire | {len(set(groups))} preuves "
          f"| rang brut moyen {np.mean([brut[s] for s in set(slot_ids)]):.0f} (médiane "
          f"{np.median([brut[s] for s in set(slot_ids)]):.0f})")

    gkf = GroupKFold(n_splits=min(3, len(set(groups))))

    def evalue(fab):
        rmod, rbrut = [], []
        for tr, te in gkf.split(Xv, y, groups):
            clf = fab()
            clf.fit(Xv[tr], y[tr])
            sc = clf.predict_proba(Xv[te])[:, 1]
            par = {}
            for j, idx in enumerate(te):
                par.setdefault(slot_ids[idx], []).append((sc[j], y[idx]))
            for s, cands in par.items():
                if not any(l for _, l in cands):
                    continue
                ordre = sorted(cands, key=lambda c: -c[0])
                rmod.append(next(r for r, (_, l) in enumerate(ordre, 1) if l))
                rbrut.append(brut[s])
        return float(np.mean(rmod)), float(np.mean(rbrut)), len(rmod)

    print()
    for nom, fab in {
        "LogReg": lambda: LogisticRegression(max_iter=2000, class_weight="balanced"),
        "RandomForest": lambda: RandomForestClassifier(n_estimators=200, class_weight="balanced",
                                                       random_state=0),
    }.items():
        rmod, rbrut, n = evalue(fab)
        print(f"[{nom:<12}] rang modèle {rmod:.2f} vs brut {rbrut:.0f} (sur {n} slots test) "
              f"→ {100*(1-rmod/rbrut):.0f}% d'appels-noyau en moins à la synthèse")

    rf = RandomForestClassifier(n_estimators=200, class_weight="balanced", random_state=0).fit(Xv, y)
    imp = sorted(zip(vec.get_feature_names_out(), rf.feature_importances_), key=lambda t: -t[1])[:8]
    print("\n[importance features] :")
    for nom, w in imp:
        print(f"    {nom:<22} {w:.3f}")
    print("# → le prior RANGE le bon terme près de la tête : la synthèse depth-2 devient tractable")
    print("#   (le noyau n'a plus qu'à valider les quelques mieux classés). pas 20 = brancher dans la synthèse.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
