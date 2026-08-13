#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Prédicteur de FÉCONDITÉ a priori (front-ouvert #2) — syntaxe SEULE vs + CONNECTIVITÉ.

`conjecturer.fecondite` mesure la fécondité A POSTERIORI. Le 1er test (features SYNTAXIQUES seules :
taille, symboles, pont) a donné un RÉSULTAT NÉGATIF (classif +4pts, R²<0) → hypothèse : la fécondité
est RELATIONNELLE (un théorème est fécond par sa CONNECTIVITÉ au graphe, pas par sa forme). Ici on
teste cette hypothèse CONSTRUCTIVEMENT en ajoutant des features de connectivité :
  · deg_aval   = nb d'implications dont l'antécédent s'unifie au conséquent de T (T peut chaîner VERS elles) ;
  · deg_amont  = nb d'implications dont le conséquent s'unifie à l'antécédent de T (elles chaînent VERS T) ;
  · deg_symbole= nb de théorèmes partageant un symbole applicatif avec T.
Si la prédiction REMONTE avec ces features → la fécondité est bien relationnelle (hypothèse confirmée).

Le noyau n'intervient pas (analyse statistique) ; frontière non concernée.
USAGE : python outils_ia/corpus/fecondite_predicteur.py [package…]
"""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[2]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))
_ICI = Path(__file__).resolve().parent
if str(_ICI) not in sys.path:
    sys.path.insert(0, str(_ICI))

import numpy as np                                            # noqa: E402
from sklearn.feature_extraction import DictVectorizer         # noqa: E402
from sklearn.ensemble import RandomForestClassifier, RandomForestRegressor  # noqa: E402
from sklearn.model_selection import cross_val_score           # noqa: E402

from conjecturer import (_corpus, fecondite, _comme_impl,      # noqa: E402
                         _taille, _apps, _match, PACKAGES)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import libres_f  # noqa: E402


def _feat_syn(thm):
    """Features STATIQUES (aucune info relationnelle)."""
    c = thm.conclusion
    tagged = hasattr(c, "tag")
    apps = _apps(c) if tagged else set()
    f = {"taille": _taille(c) if tagged else 0, "n_app": len(apps), "is_impl": 0}
    ab = _comme_impl(c)
    if ab:
        f["is_impl"] = 1
        aA, aB = _apps(ab[0]), _apps(ab[1])
        u = aA | aB
        f["pont"] = round(1 - len(aA & aB) / len(u), 2) if u else 0.0
        f["taille_A"], f["taille_B"] = _taille(ab[0]), _taille(ab[1])
    for s in apps:
        f[f"has_{s}"] = 1
    return f


def _feat_rel(thm, impls, deg_sym):
    """Features de CONNECTIVITÉ (degrés de chaînage dans le graphe potentiel)."""
    c = thm.conclusion
    f = {"deg_symbole": deg_sym}
    ab = _comme_impl(c)
    if ab:
        A, B = ab
        aval = sum(1 for (_, T2, A2, _) in impls
                   if _match(A2, B, {}, libres_f(T2.conclusion)))
        amont = sum(1 for (_, T2, _, B2) in impls
                    if _match(B2, A, {}, libres_f(T2.conclusion)))
        f["deg_aval"], f["deg_amont"] = aval, amont
    else:
        f["deg_aval"], f["deg_amont"] = 0, 0
    return f


def _evaluer(Xv, y, yb, cv):
    clf = RandomForestClassifier(n_estimators=300, class_weight="balanced", random_state=0)
    acc = cross_val_score(clf, Xv, yb, cv=cv).mean()
    reg = RandomForestRegressor(n_estimators=300, random_state=0)
    r2 = cross_val_score(reg, Xv, y, cv=cv, scoring="r2").mean()
    return acc, r2


def main(argv):
    packages = [a for a in argv[1:] if not a.startswith("--")] or PACKAGES
    print("# PRÉDICTEUR DE FÉCONDITÉ — syntaxe seule vs + connectivité", file=sys.stderr)
    impls, preuve_de = _corpus(packages)
    usage, _info = fecondite(impls, preuve_de)

    items = list(preuve_de.items())                          # (conclusion, (nom, thm))
    apps_par = [(_apps(c) if hasattr(c, "tag") else set()) for c, _ in items]
    y = np.array([usage.get(nom, 0) for _, (nom, _) in items])

    syn, rel = [], []
    for i, (c, (nom, thm)) in enumerate(items):
        deg_sym = sum(1 for j, ap in enumerate(apps_par) if j != i and (apps_par[i] & ap))
        fs = _feat_syn(thm)
        syn.append(fs)
        rel.append({**fs, **_feat_rel(thm, impls, deg_sym)})

    pos = y[y > 0]
    seuil = max(2, int(np.percentile(pos, 75))) if pos.size else 1
    yb = (y >= seuil).astype(int)
    n_pos = int(yb.sum())
    print(f"# {len(y)} théorèmes | usage max {int(y.max())}, moyenne {y.mean():.1f} | "
          f"seuil-fécond ≥{seuil} → {n_pos} féconds / {len(y) - n_pos} non")
    if n_pos < 2 or len(y) - n_pos < 2:
        print("# pas assez de variété.")
        return 0
    cv = max(2, min(5, n_pos, len(y) - n_pos))
    base = max(yb.mean(), 1 - yb.mean())

    vec_s, vec_r = DictVectorizer(sparse=False), DictVectorizer(sparse=False)
    Xs, Xr = vec_s.fit_transform(syn), vec_r.fit_transform(rel)
    acc_s, r2_s = _evaluer(Xs, y, yb, cv)
    acc_r, r2_r = _evaluer(Xr, y, yb, cv)

    print(f"\n# baseline (classe majoritaire) : {base:.3f}")
    print(f"#  {'jeu de features':<26} {'accuracy':>9} {'R²':>8}")
    print(f"#  {'syntaxe seule':<26} {acc_s:>9.3f} {r2_s:>8.3f}")
    print(f"#  {'+ connectivité (relation)':<26} {acc_r:>9.3f} {r2_r:>8.3f}")

    rf = RandomForestRegressor(n_estimators=300, random_state=0).fit(Xr, y)
    imp = sorted(zip(vec_r.get_feature_names_out(), rf.feature_importances_), key=lambda t: -t[1])[:8]
    print("\n# features les plus prédictives (jeu + connectivité) :")
    for nom, w in imp:
        print(f"#   {w:.3f}  {nom}")

    lift = (acc_r - acc_s, r2_r - r2_s)
    degre_domine = any(n.startswith("deg_") for n, _ in imp[:3])
    print(f"\n# VERDICT (honnête) : Δacc {lift[0]:+.3f}, ΔR² {lift[1]:+.3f} ; degrés en tête = {degre_domine}.")
    if degre_domine and r2_r > r2_s + 0.05:
        print("# → DIRECTION confirmée : la fécondité est RELATIONNELLE (les degrés de chaînage écrasent")
        print("#   la syntaxe, l'erreur de régression s'effondre). MAIS le degré LOCAL (1 saut) ne suffit")
        print(f"#   pas à prédire la magnitude (R²={r2_r:.2f} encore <0). Le degré est un PRIOR de tri")
        print("#   utilisable ; la prédiction exacte exige la structure PROFONDE du graphe (multi-sauts/GNN).")
    else:
        print("# → même la connectivité locale ne suffit pas : structure de graphe profonde requise (GNN).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
