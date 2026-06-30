#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Politique SÉQUENTIELLE : reconstruire une preuve K-corrompue — marche guidée (pivot, pas 12).

Le pas 10 répare UN trou (rang 1.00). Ici : on supprime K pas, et on RECONSTRUIT en
chaînant la repair-policy apprise — pour chaque trou, le modèle classe les candidats
(signal data-flow), on insère le top-1, et le NOYAU valide la reconstruction complète.
C'est la marche guidée multi-pas sur le DAG = le comportement du générateur.

On entraîne sur des modules et on TESTE la reconstruction sur des preuves TENUES À L'ÉCART
(aucune fuite). Métrique : taux de reconstruction valide (noyau OK) vs K = nb de pas
supprimés. Le modèle ne reçoit JAMAIS le noyau pendant la reconstruction ; le noyau ne
juge qu'à la fin (vérification exacte) — c'est exactement generate(politique)+verify(noyau).

Outillage seulement (outils_ia/) ; le noyau reste l'oracle ; aucun Theoreme forgé.
USAGE : python outils_ia/corpus/proto_sequential.py
"""
from __future__ import annotations

import ast
import importlib
import inspect
import random
import sys
import textwrap
from bisect import bisect_left
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

import numpy as np                                       # noqa: E402
from sklearn.feature_extraction import DictVectorizer    # noqa: E402
from sklearn.ensemble import RandomForestClassifier      # noqa: E402

from proto_mutation_verify import _cible_de, _rebuild    # noqa: E402
from gen_paires_corruption import _statut                # noqa: E402
from repair_learned import (_fn_principale, _assignes, _charges, _n_args, _uses_N)  # noqa: E402

TRAIN = [
    "bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple",
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_projection_fonctionnelle",
    "bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide",
]
TEST = [
    "bourbaki.ensembles.ii_3_correspondances.ensembles_identite_neutre",
    "bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee_monotone",
]


def _feats(corrompu: list, idx: int, cand) -> dict:
    """Feature-dict pour insérer `cand` au trou d'indice `idx` du corps `corrompu`."""
    n = len(corrompu) + 1
    prev_fn = _fn_principale(corrompu[idx - 1]) if idx > 0 else "⊤"
    next_fn = _fn_principale(corrompu[idx]) if idx < len(corrompu) else "⊥"
    assignes_tous = set().union(*(_assignes(s) for s in corrompu)) if corrompu else set()
    lues_apres = set().union(*(_charges(s) for s in corrompu[idx:])) if corrompu[idx:] else set()
    manquantes = lues_apres - assignes_tous
    return {"cand_fn": _fn_principale(cand), "prev_fn": prev_fn, "next_fn": next_fn,
            "pos_ratio": round(idx / n, 2),
            "fournit_manquante": int(bool(_assignes(cand) & manquantes)),
            "n_args": _n_args(cand), "uses_N": _uses_N(cand),
            "n_assignes": len(_assignes(cand)), "n_manquantes": len(manquantes)}


def _theoremes(mod):
    for name in getattr(mod, "__all__", []):
        if not name.endswith("_cible") and callable(getattr(mod, name, None)) \
                and _cible_de(mod, name) is not None:
            try:
                fdef = ast.parse(textwrap.dedent(inspect.getsource(getattr(mod, name)))).body[0]
            except Exception:
                continue
            body = fdef.body
            start = 1 if (body and isinstance(body[0], ast.Expr)
                          and isinstance(getattr(body[0], "value", None), ast.Constant)) else 0
            yield name, fdef, body, start


def collecte_train(modules):
    X, y = [], []
    for modname in modules:
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        for name, fdef, body, start in _theoremes(mod):
            cible = _cible_de(mod, name)
            pool = body[start:]
            for i in range(start, len(body)):
                corrompu = body[:i] + body[i + 1:]
                oracle = ast.dump(body[i])
                for cand in pool:
                    essai = corrompu[:i] + [cand] + corrompu[i:]
                    X.append(_feats(corrompu, i, cand))
                    y.append(int(_statut(mod, name, _rebuild(fdef, essai), cible) == "OK"))
    return X, np.array(y)


def reconstruire(mod, name, fdef, body, start, model, vec, K, rng) -> bool:
    """Supprime K pas, reconstruit par top-1 modèle à chaque trou, renvoie noyau OK ?"""
    cible = _cible_de(mod, name)
    pool = body[start:]
    positions = list(range(start, len(body)))
    if len(positions) < K:
        return None
    gaps = sorted(rng.sample(positions, K))
    remaining = [body[i] for i in range(len(body)) if i not in gaps]
    kept = [i for i in range(len(body)) if i not in gaps]
    choix = {}                                            # gap original index -> candidat choisi
    for g in gaps:
        idx = bisect_left(kept, g)                        # position d'insertion dans `remaining`
        scores = model.predict_proba(vec.transform([_feats(remaining, idx, c) for c in pool]))[:, 1]
        choix[g] = pool[int(np.argmax(scores))]           # top-1 du modèle pour ce trou
    # reconstruire le corps complet : statements gardés + candidats choisis aux trous
    recon, gi = [], 0
    for i in range(len(body)):
        if i in choix:
            recon.append(choix[i])
        else:
            recon.append(body[i])
    return _statut(mod, name, _rebuild(fdef, recon), cible) == "OK"


def main(argv):
    print("# entraînement repair-policy (RandomForest) sur modules d'entraînement…", file=sys.stderr)
    X, y = collecte_train(TRAIN)
    vec = DictVectorizer(sparse=False)
    Xv = vec.fit_transform(X)
    model = RandomForestClassifier(n_estimators=200, class_weight="balanced", random_state=0).fit(Xv, y)
    print(f"# train : {len(y)} exemples, {y.sum()} (+) | test sur preuves TENUES À L'ÉCART")
    rng = random.Random(20260630)
    par_K = {1: [0, 0], 2: [0, 0], 3: [0, 0]}             # K -> [succès, total]
    for modname in TEST:
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        for name, fdef, body, start in _theoremes(mod):
            for K in (1, 2, 3):
                for _ in range(5):                        # 5 essais aléatoires par (théorème, K)
                    ok = reconstruire(mod, name, fdef, body, start, model, vec, K, rng)
                    if ok is None:
                        continue
                    par_K[K][1] += 1
                    par_K[K][0] += int(ok)
    print("\n[séquentiel] reconstruction valide (noyau OK) par nb de pas supprimés K :")
    for K, (s, t) in par_K.items():
        if t:
            print(f"    K={K} : {s}/{t} reconstruites  ({100*s//t}%)")
    print("# = marche guidée multi-pas : la politique apprise propose, le noyau valide à la fin.")
    print("# (K=1 ≈ parfait ; la chute avec K mesure l'ambiguïté d'assignation multi-trous.)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
