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
    recon = [choix[i] if i in choix else body[i] for i in range(len(body))]
    return _statut(mod, name, _rebuild(fdef, recon), cible) == "OK"


def _partial(body, gaps, filled, g):
    """Corps partiel : gardés + candidats DÉJÀ remplis ; trous non-remplis ôtés ;
    `g` laissé comme HOLE. Renvoie (statements, indice d'insertion de g)."""
    stmts, idx_g = [], None
    for i in range(len(body)):
        if i == g:
            idx_g = len(stmts)                            # le trou g est ici
            continue
        if i in gaps and i not in filled:
            continue                                      # autre trou non-rempli : toujours manquant
        stmts.append(filled[i] if i in filled else body[i])
    return stmts, idx_g


def reconstruire_iteratif(mod, name, fdef, body, start, model, vec, K, rng):
    """Greedy + recompute : remplir le trou de plus haute confiance, recalculer, recommencer."""
    cible = _cible_de(mod, name)
    pool = body[start:]
    positions = list(range(start, len(body)))
    if len(positions) < K:
        return None
    gaps = sorted(rng.sample(positions, K))
    filled, restants = {}, set(gaps)
    while restants:
        best = (-1.0, None, None)                          # (score, gap, candidat)
        for g in restants:
            stmts, idx_g = _partial(body, gaps, filled, g)
            scores = model.predict_proba(vec.transform([_feats(stmts, idx_g, c) for c in pool]))[:, 1]
            j = int(np.argmax(scores))
            if scores[j] > best[0]:
                best = (float(scores[j]), g, pool[j])
        filled[best[1]] = best[2]                          # remplir le trou le plus sûr
        restants.discard(best[1])
    recon = [filled[i] if i in filled else body[i] for i in range(len(body))]
    return _statut(mod, name, _rebuild(fdef, recon), cible) == "OK"


def reconstruire_beam(mod, name, fdef, body, start, model, vec, K, rng, B=4):
    """BEAM search (pas 15) : au lieu de s'engager sur UNE trajectoire (greedy top-1), garder les
    B reconstructions partielles les plus probables. À chaque pas : pour chaque beam, pour chaque
    trou restant, étendre par les B meilleurs candidats du modèle ; ne conserver que les B états
    de plus haut score (somme de log-probas). Le NOYAU ne juge QU'À LA FIN, sur les ≤B beams
    complets — succès si l'un valide. Lève l'ambiguïté multi-trous mieux que le greedy à 1 chemin."""
    cible = _cible_de(mod, name)
    pool = body[start:]
    positions = list(range(start, len(body)))
    if len(positions) < K:
        return None
    gaps = sorted(rng.sample(positions, K))
    beam = [(0.0, {}, frozenset(gaps))]                    # (score, filled: {gap->idx pool}, restants)
    for _ in range(K):
        enfants = {}                                       # clé = frozenset(filled.items()) → meilleur état
        for score, filled, restants in beam:
            filled_stmts = {g: pool[ci] for g, ci in filled.items()}
            for g in restants:
                stmts, idx_g = _partial(body, gaps, filled_stmts, g)
                probs = model.predict_proba(vec.transform([_feats(stmts, idx_g, c) for c in pool]))[:, 1]
                for ci in np.argsort(probs)[::-1][:B]:     # B meilleurs candidats pour ce trou
                    nf = dict(filled)
                    nf[g] = int(ci)
                    cle = frozenset(nf.items())
                    s2 = score + float(np.log(probs[ci] + 1e-9))
                    if cle not in enfants or enfants[cle][0] < s2:
                        enfants[cle] = (s2, nf, restants - {g})
        beam = sorted(enfants.values(), key=lambda e: -e[0])[:B]
    for score, filled, restants in beam:                   # vérifier les beams complets (≤B appels noyau)
        recon = [pool[filled[i]] if i in filled else body[i] for i in range(len(body))]
        if _statut(mod, name, _rebuild(fdef, recon), cible) == "OK":
            return True
    return False


def main(argv):
    print("# entraînement repair-policy (RandomForest) sur modules d'entraînement…", file=sys.stderr)
    X, y = collecte_train(TRAIN)
    vec = DictVectorizer(sparse=False)
    Xv = vec.fit_transform(X)
    model = RandomForestClassifier(n_estimators=200, class_weight="balanced", random_state=0).fit(Xv, y)
    print(f"# train : {len(y)} exemples, {y.sum()} (+) | test sur preuves TENUES À L'ÉCART")
    rng = random.Random(20260630)
    KS = (1, 2, 3, 4, 5)                                  # on pousse jusqu'à K=5 pour trouver la frontière
    indep = {k: [0, 0] for k in KS}                       # K -> [succès, total]
    iterv = {k: [0, 0] for k in KS}
    beam = {k: [0, 0] for k in KS}
    for modname in TEST:
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        for name, fdef, body, start in _theoremes(mod):
            for K in KS:
                for _ in range(8):                        # 8 essais aléatoires par (théorème, K)
                    a = reconstruire(mod, name, fdef, body, start, model, vec, K, rng)
                    b = reconstruire_iteratif(mod, name, fdef, body, start, model, vec, K, rng)
                    c = reconstruire_beam(mod, name, fdef, body, start, model, vec, K, rng, B=4)
                    for res, acc in ((a, indep), (b, iterv), (c, beam)):
                        if res is not None:
                            acc[K][1] += 1
                            acc[K][0] += int(res)
    print("\n[séquentiel] reconstruction valide (noyau OK) — INDÉPENDANT vs ITÉRATIF vs BEAM(B=4) :")
    for K in KS:
        si, ti = indep[K]
        sj, tj = iterv[K]
        sk, tk = beam[K]
        if ti and tj and tk:
            print(f"    K={K} : indép {si:>2}/{ti} ({100*si//ti:>3}%)  →  itératif {sj:>2}/{tj} "
                  f"({100*sj//tj:>3}%)  →  beam {sk:>2}/{tk} ({100*sk//tk:>3}%)")
    print("# = marche guidée multi-pas : greedy+recompute relève déjà K≥2 ; le BEAM garde les B")
    print("# trajectoires les plus probables (noyau juge ≤B beams complets à la fin) pour relever K=3.")
    print("# (generate(politique) + verify(noyau) : le noyau ne juge qu'à la fin.)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
