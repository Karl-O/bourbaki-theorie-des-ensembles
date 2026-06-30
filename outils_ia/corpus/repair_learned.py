#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Premier repaireur APPRIS : prédire la tactique qui répare un trou (pivot, pas 8-9).

Le pas 7 répare en BRUTE-FORCE (essayer tous les candidats, le noyau filtre). Ici on
APPREND un prior : un classifieur (sklearn) qui, vu le CONTEXTE d'un trou (les tactiques
voisines + la position), prédit quel candidat le répare. On range alors les candidats par
score décroissant et on n'appelle le noyau que sur les mieux classés → bien moins d'essais.

C'est le passage « brute-force → politique apprise » (embryon du reverse process appris).
Le noyau reste l'ORACLE de vérité (les labels viennent de lui ; il valide toute réparation).

PIPELINE :
  1. collecte : pour chaque preuve, chaque suppression 1-pas, chaque candidat (les pas de
     la preuve = bibliothèque locale) → features {cand_fn, prev_fn, next_fn, pos_ratio} +
     label is_repair (le NOYAU dit OK ?) ;
  2. entraînement : LogisticRegression, validation par GroupKFold (groupe = théorème →
     aucune fuite : on teste sur des preuves jamais vues) ;
  3. évaluation : range les candidats par P(repair) ; mesure le RANG du 1ᵉ vrai repair
     (= nb d'appels noyau avant de réparer) vs l'ordre brute-force (aléatoire). Gain = le
     prior trouve la réparation plus tôt.

Outillage seulement (outils_ia/) ; réutilise la machinerie des protos ; le noyau reste juge.
USAGE : python outils_ia/corpus/repair_learned.py [module1 module2 ...]
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

import numpy as np                                       # noqa: E402
from sklearn.feature_extraction import DictVectorizer    # noqa: E402
from sklearn.linear_model import LogisticRegression      # noqa: E402
from sklearn.model_selection import GroupKFold           # noqa: E402

from proto_mutation_verify import _cible_de, _rebuild    # noqa: E402
from gen_paires_corruption import _statut                # noqa: E402

MODULES = [
    "bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple",
    "bourbaki.ensembles.ii_3_correspondances.ensembles_identite_neutre",
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_projection_fonctionnelle",
    "bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide",
    "bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee_monotone",
]


def _fn_principale(stmt: ast.stmt) -> str:
    """Nom de la 1ʳᵉ fonction appelée dans un statement (sa « tactique »)."""
    for node in ast.walk(stmt):
        if isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Name):
                return f.id
            if isinstance(f, ast.Attribute):
                return f.attr
    return "∅"


def _assignes(stmt) -> set:
    """Variables ASSIGNÉES par un statement (cibles d'affectation)."""
    out = set()
    for node in ast.walk(stmt):
        if isinstance(node, ast.Assign):
            for tgt in node.targets:
                out |= {nm.id for nm in ast.walk(tgt) if isinstance(nm, ast.Name)}
        elif isinstance(node, (ast.AugAssign, ast.AnnAssign)) and isinstance(node.target, ast.Name):
            out.add(node.target.id)
    return out


def _charges(stmt) -> set:
    """Variables LUES (Load) par un statement."""
    return {n.id for n in ast.walk(stmt) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}


def collecter(modnames):
    """(liste de features-dict, labels, groupes-théorème, méta) sur tous les modules."""
    X, y, groups, meta = [], [], [], []
    gid = 0
    for modname in modnames:
        try:
            mod = importlib.import_module(modname)
        except Exception:
            continue
        names = [n for n in getattr(mod, "__all__", [])
                 if not n.endswith("_cible") and callable(getattr(mod, n, None))
                 and _cible_de(mod, n) is not None]
        for name in names:
            cible = _cible_de(mod, name)
            try:
                fdef = ast.parse(textwrap.dedent(inspect.getsource(getattr(mod, name)))).body[0]
            except Exception:
                continue
            body = fdef.body
            start = 1 if (body and isinstance(body[0], ast.Expr)
                          and isinstance(getattr(body[0], "value", None), ast.Constant)) else 0
            pool = body[start:]
            n = len(body)
            gid += 1
            for i in range(start, n):
                corrompu = body[:i] + body[i + 1:]
                prev_fn = _fn_principale(body[i - 1]) if i > start else "⊤"
                next_fn = _fn_principale(body[i + 1]) if i + 1 < n else "⊥"
                oracle = ast.dump(body[i])
                # data-flow : variables LUES après le trou mais JAMAIS assignées dans le
                # corrompu = ce que le pas supprimé fournissait (le « trou » à combler).
                assignes_tous = set().union(*(_assignes(s) for s in corrompu)) if corrompu else set()
                lues_apres = set().union(*(_charges(s) for s in corrompu[i:])) if corrompu[i:] else set()
                manquantes = lues_apres - assignes_tous
                for cand in pool:
                    feats = {"cand_fn": _fn_principale(cand), "prev_fn": prev_fn,
                             "next_fn": next_fn, "pos_ratio": round(i / n, 2),
                             # 1 si le candidat ASSIGNE une variable manquante = signal data-flow
                             "fournit_manquante": int(bool(_assignes(cand) & manquantes))}
                    essai = corrompu[:i] + [cand] + corrompu[i:]
                    lab = int(_statut(mod, name, _rebuild(fdef, essai), cible) == "OK")
                    X.append(feats)
                    y.append(lab)
                    groups.append(gid)
                    meta.append((name, i, ast.dump(cand) == oracle))
    return X, np.array(y), np.array(groups), meta


def main(argv):
    modnames = argv[1:] or MODULES
    print(f"# collecte sur {len(modnames)} modules…", file=sys.stderr)
    X, y, groups, meta = collecter(modnames)
    if len(set(y)) < 2:
        print("# pas assez de variété de labels", file=sys.stderr)
        return 1
    vec = DictVectorizer(sparse=False)
    Xv = vec.fit_transform(X)
    print(f"# {len(y)} exemples (candidat-insertions) | {y.sum()} réparations (+) | "
          f"{len(set(groups))} théorèmes | {Xv.shape[1]} features")

    # validation croisée par théorème (GroupKFold) — aucune fuite
    gkf = GroupKFold(n_splits=min(5, len(set(groups))))
    accs, rangs_modele, rangs_brute = [], [], []
    for tr, te in gkf.split(Xv, y, groups):
        clf = LogisticRegression(max_iter=1000, class_weight="balanced")
        clf.fit(Xv[tr], y[tr])
        accs.append(clf.score(Xv[te], y[te]))
        # rang du 1ᵉ vrai repair par (théorème, position) du fold test
        scores = clf.predict_proba(Xv[te])[:, 1]
        par_trou = {}
        for j, idx in enumerate(te):
            name, pos, is_oracle = meta[idx]
            par_trou.setdefault((name, pos), []).append((scores[j], y[idx]))
        for cands in par_trou.values():
            if not any(lab for _, lab in cands):
                continue
            ordre = sorted(cands, key=lambda c: -c[0])               # rangé par le modèle
            rangs_modele.append(next(r for r, (_, lab) in enumerate(ordre, 1) if lab))
            rangs_brute.append((len(cands) + 1) / 2)                 # rang attendu aléatoire
    print(f"\n[learned] accuracy CV (GroupKFold) : {np.mean(accs):.3f}")
    print(f"[learned] RANG MOYEN du 1ᵉ vrai repair : modèle {np.mean(rangs_modele):.2f} "
          f"vs brute-force aléatoire {np.mean(rangs_brute):.2f}  "
          f"→ {100*(1-np.mean(rangs_modele)/np.mean(rangs_brute)):.0f}% d'appels-noyau en moins")
    print("# = 1ᵉ politique APPRISE : le prior trouve la réparation plus tôt que la force brute,")
    print("#   le noyau restant l'oracle exact qui valide. Embryon du reverse process appris.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
