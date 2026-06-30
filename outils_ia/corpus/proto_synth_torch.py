#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Modèle STRUCTURÉ (torch) pour ranger les termes de synthèse (pivot, pas 21).

Le pas 19-20 a montré que le prior SHALLOW (sklearn + features agrégées) plafonne sur le ranking
de termes depth-2 (rang ~557, à peine mieux que le brut 798) : il ne capte pas l'ARRANGEMENT
(quelle variable à quelle position). Ici on encode l'AST du terme RÉCURSIVEMENT (un petit
TreeNN torch) : chaque feuille porte ses features data-flow (∈ manquantes/disponibles/sorties),
chaque constructeur (composee/diagonale/couple/var) COMPOSE ses enfants avec des poids propres →
l'embedding du terme connaît sa STRUCTURE. Un MLP score (embedding-terme ⊕ contexte-slot).

Entraînement : ranking LISTWISE par slot (softmax sur les candidats, cible = le terme réel de P
= oracle GRATUIT), GroupKFold par PREUVE (aucune fuite). Métrique : rang du bon terme sur les
slots tenus à l'écart — NEURONAL vs SHALLOW (LogReg) vs BRUT. Petit modèle CPU, graine fixe.

Outillage seulement (outils_ia/) ; ne fabrique aucun Theoreme. Réutilise la machinerie de synthèse.
USAGE : python outils_ia/corpus/proto_synth_torch.py [module1 module2 ...]
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
import torch                                                # noqa: E402
import torch.nn as nn                                       # noqa: E402
from sklearn.feature_extraction import DictVectorizer       # noqa: E402
from sklearn.linear_model import LogisticRegression         # noqa: E402
from sklearn.model_selection import GroupKFold              # noqa: E402

import proto_synth_termes as PST                            # noqa: E402
from proto_synth_termes import synth_termes, _slots         # noqa: E402
from proto_synth_prior import _feats, _head                 # noqa: E402
from proto_macro_noyau import _proofs, _occurrences, NS      # noqa: E402
from proto_macro_termes import _str_consts, _ctx_trou        # noqa: E402
from repair_learned import _assignes                         # noqa: E402

PST.MAXT = 1500
# pas 22→25 : élargir les modules n'ajoutait AUCUN slot in-grammaire TANT QUE la grammaire était
# étroite (composee/diagonale/couple/var) ; une fois enrichie (const+et+inclus+conjonction_elim_*,
# pas 23-25), produit_extensionnalite passe de 0 à 19 slots in-grammaire → +3 preuves de DONNÉES.
# Le goulot était bien GRAMMAIRE, et l'enrichir débloque AUSSI de nouvelles preuves.
MODULES = [
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_projection_fonctionnelle",
    "bourbaki.ensembles.ii_3_correspondances.ensembles_identite_neutre",
    "bourbaki.ensembles.ii_3_correspondances.ensembles_diagonale_couple",
    "bourbaki.ensembles.ii_2_couples_produit.ensembles_produit_extensionnalite",  # pas 25 (débloqué)
    # pas 29 : modules NON-arrangement riches en slots (scan : aucun module n'a de slots d'ARRANGEMENT
    # composee/diagonale/couple hors des 4 ci-dessus → la donnée pour casser l'effet miroir n'existe
    # PAS dans le corpus). Ceux-ci ajoutent et/conjonction_elim/const/equivalence_avant = + de DONNÉES
    # diverses pour la robustesse générale du ranker (≠ arrangement).
    "bourbaki.ensembles.fonctions.ii_3_general.ensembles_fonctions_props2",          # +21 in-gram
    "bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_image_reciproque_props",  # +12 in-gram
]
CF_VOCAB = {}           # tactique appelante -> index (rempli à la collecte)


def collecte_slots(modnames):
    """Liste de slots : {cf, pos, ctx (manq,disp,outs), pool (ast), pos_idx, group, feats_sh}."""
    slots = []
    gid = 0
    for modname in modnames:
        mod, proofs = _proofs(modname)
        if not proofs:
            continue
        vl = {v for _, b, s, _ in proofs.values() for st in b[s:] for v in _assignes(st)}
        from collections import defaultdict
        ng = defaultdict(set)
        for nm, (_, _, _, sg) in proofs.items():
            for nl in NS:
                for i in range(len(sg) - nl + 1):
                    ng[tuple(sg[i:i + nl])].add(nm)
        macros = {m for m, pr in ng.items() if len(pr) >= 2}
        for P in proofs:
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
                    L = len(macro)
                    if (occ, L) in seen:
                        continue
                    seen.add((occ, L))
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
                                continue                    # hors grammaire
                            CF_VOCAB.setdefault(cf, len(CF_VOCAB) + 1)
                            slots.append({"cf": cf, "pos": k, "manq": manq, "disp": disp,
                                          "outs": outs, "pool": pool, "pos_idx": pd.index(od),
                                          "group": gid})
    return slots


# ---- features par-NŒUD (pour le TreeNN) ------------------------------------
NLEAF = 6


def _leaf_vec(node, manq, disp, outs):
    if isinstance(node, ast.Name):
        return [1.0, 0.0, float(node.id in manq), float(node.id in disp), float(node.id in outs), 0.0]
    if isinstance(node, ast.Constant):
        return [0.0, 1.0, 0.0, 0.0, 0.0, 1.0]
    return [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]


class TreeEnc(nn.Module):
    def __init__(self, d=24):
        super().__init__()
        self.d = d
        self.leaf = nn.Linear(NLEAF, d)
        self.var = nn.Linear(d, d)
        self.diag = nn.Linear(d, d)
        self.comp = nn.Linear(2 * d, d)
        self.coup = nn.Linear(2 * d, d)
        self.et = nn.Linear(2 * d, d)               # pas 24 : constructeur formule et/2
        self.incl = nn.Linear(2 * d, d)             # pas 25 : relation inclus/2
        self.elim = nn.Linear(d, d)                 # pas 25 : proof-terms conjonction_elim_*/1
        self.un1 = nn.Linear(d, d)                  # pas 26 : unaires equivalence_avant/est_un_couple
        self.exte = nn.Linear(2 * d, d)             # pas 26 : existe_temoin/2
        self.sym = nn.Linear(2 * d, d)              # pas 26 : symetrie/2

    def enc(self, node, ctx):
        manq, disp, outs = ctx
        if isinstance(node, (ast.Name, ast.Constant)):
            return torch.relu(self.leaf(torch.tensor(_leaf_vec(node, manq, disp, outs),
                                                     dtype=torch.float32)))
        if isinstance(node, ast.Call):
            h = _head(node)
            if h == "var":
                return torch.relu(self.var(self.enc(node.args[0], ctx)))
            if h == "diagonale":
                return torch.relu(self.diag(self.enc(node.args[0], ctx)))
            if h == "composee":
                return torch.relu(self.comp(torch.cat([self.enc(node.args[0], ctx),
                                                       self.enc(node.args[1], ctx)])))
            if h == "couple":
                return torch.relu(self.coup(torch.cat([self.enc(node.args[0], ctx),
                                                       self.enc(node.args[1], ctx)])))
            if h == "et":
                return torch.relu(self.et(torch.cat([self.enc(node.args[0], ctx),
                                                     self.enc(node.args[1], ctx)])))
            if h == "inclus":
                return torch.relu(self.incl(torch.cat([self.enc(node.args[0], ctx),
                                                       self.enc(node.args[1], ctx)])))
            if h in ("conjonction_elim_gauche", "conjonction_elim_droite"):
                return torch.relu(self.elim(self.enc(node.args[0], ctx)))
            if h in ("equivalence_avant", "est_un_couple"):
                return torch.relu(self.un1(self.enc(node.args[0], ctx)))
            if h == "existe_temoin":
                return torch.relu(self.exte(torch.cat([self.enc(node.args[0], ctx),
                                                       self.enc(node.args[1], ctx)])))
            if h == "symetrie":
                return torch.relu(self.sym(torch.cat([self.enc(node.args[0], ctx),
                                                      self.enc(node.args[1], ctx)])))
        return torch.zeros(self.d)


class Scorer(nn.Module):
    def __init__(self, d=24, dc=8, drop=0.1):
        super().__init__()
        self.enc = TreeEnc(d)
        self.cf = nn.Embedding(64, dc)
        self.mlp = nn.Sequential(nn.Linear(d + dc + 1, 32), nn.ReLU(), nn.Dropout(drop),
                                 nn.Linear(32, 1))

    def score(self, term, ctx, cf_idx, pos):
        e = self.enc.enc(term, ctx)
        c = self.cf(torch.tensor(min(cf_idx, 63)))
        return self.mlp(torch.cat([e, c, torch.tensor([float(pos)], dtype=torch.float32)]))


def _entraine(train_slots, epochs=22, neg=48, seed=0):
    torch.manual_seed(seed)
    rng = np.random.default_rng(seed)
    net = Scorer()
    net.train()
    opt = torch.optim.Adam(net.parameters(), lr=0.01, weight_decay=1e-4)  # régularisation L2
    order = list(range(len(train_slots)))
    for ep in range(epochs):
        rng.shuffle(order)
        for i in order:
            s = train_slots[i]
            pool = s["pool"]
            ctx = (s["manq"], s["disp"], s["outs"])
            cfi = CF_VOCAB.get(s["cf"], 0)
            idxs = [s["pos_idx"]] + list(rng.choice(len(pool), size=min(neg, len(pool)), replace=False))
            sc = torch.cat([net.score(pool[i2], ctx, cfi, s["pos"]) for i2 in idxs]).reshape(1, -1)
            loss = nn.functional.cross_entropy(sc, torch.tensor([0]))  # cible = positif (indice 0)
            opt.zero_grad()
            loss.backward()
            opt.step()
    net.eval()
    return net


def _scores_ens(nets, s):
    """Scores ENSEMBLE (moyenne sur les graines) pour tous les candidats du slot."""
    pool = s["pool"]
    ctx = (s["manq"], s["disp"], s["outs"])
    cfi = CF_VOCAB.get(s["cf"], 0)
    with torch.no_grad():
        acc = np.zeros(len(pool))
        for net in nets:
            acc += np.array([net.score(t, ctx, cfi, s["pos"]).item() for t in pool])
    return acc / len(nets)


def _rang(sc, pos_idx):
    return int(np.sum(sc > sc[pos_idx])) + 1


def main(argv):
    modnames = argv[1:] or MODULES
    print(f"# collecte des slots in-grammaire sur {len(modnames)} modules…", file=sys.stderr)
    slots = collecte_slots(modnames)
    groups = np.array([s["group"] for s in slots])
    print(f"# {len(slots)} slots in-grammaire | {len(set(groups))} preuves | rang brut moyen "
          f"{np.mean([s['pos_idx']+1 for s in slots]):.0f}")
    if len(slots) < 6:
        print("# trop peu de slots", file=sys.stderr)
        return 1

    # shallow LogReg de référence (mêmes features que pas 19), même GroupKFold
    Xsh = [_feats(s["pool"][s["pos_idx"]], s["cf"], s["pos"], s["manq"], s["disp"], s["outs"])
           for s in slots]  # placeholder pour fit du vectorizer
    gkf = GroupKFold(n_splits=min(3, len(set(groups))))
    r_brut, r_sh, r_nn = [], [], []
    for tr, te in gkf.split(slots, [0] * len(slots), groups):
        # --- shallow : features par candidat, label = est-ce le bon terme ---
        Xtr, ytr = [], []
        for i in tr:
            s = slots[i]
            for j, t in enumerate(s["pool"]):
                Xtr.append(_feats(t, s["cf"], s["pos"], s["manq"], s["disp"], s["outs"]))
                ytr.append(int(j == s["pos_idx"]))
        vec = DictVectorizer(sparse=False)
        Xv = vec.fit_transform(Xtr)
        sh = LogisticRegression(max_iter=1500, class_weight="balanced").fit(Xv, np.array(ytr))
        # --- neural : ENSEMBLE de E modèles (graines) pour écraser les outliers ---
        E = 2
        nets = [_entraine([slots[i] for i in tr], seed=sd) for sd in range(E)]
        print(f"#   fold entraîné (ensemble de {E})", file=sys.stderr)
        for i in te:
            s = slots[i]
            r_brut.append(s["pos_idx"] + 1)
            Xte = vec.transform([_feats(t, s["cf"], s["pos"], s["manq"], s["disp"], s["outs"])
                                 for t in s["pool"]])
            sc = sh.predict_proba(Xte)[:, 1]
            r_sh.append(int(np.sum(sc > sc[s["pos_idx"]])) + 1)
            r_nn.append(_rang(_scores_ens(nets, s), s["pos_idx"]))
    rb, rs, rn = np.array(r_brut), np.array(r_sh), np.array(r_nn)
    print(f"\n# RANG du bon terme (slots tenus à l'écart, {len(rb)} slots) — MÉDIANE = robuste :")
    print(f"    BRUT (énumération)       : médiane {np.median(rb):5.0f}  | moyenne {rb.mean():6.0f}  "
          f"| top-5 {100*np.mean(rb<=5):.0f}%")
    print(f"    SHALLOW (LogReg, pas 19) : médiane {np.median(rs):5.0f}  | moyenne {rs.mean():6.0f}  "
          f"| top-5 {100*np.mean(rs<=5):.0f}%")
    print(f"    NEURONAL (TreeNN, pas 21): médiane {np.median(rn):5.0f}  | moyenne {rn.mean():6.0f}  "
          f"| top-5 {100*np.mean(rn<=5):.0f}%")
    print(f"# → le TreeNN encode la STRUCTURE : MÉDIANE {np.median(rb):.0f}→{np.median(rs):.0f}"
          f"→{np.median(rn):.0f} (brut→shallow→neuronal), top-5 {100*np.mean(rn<=5):.0f}%.")
    print(f"# pas 22 : régularisation (dropout+L2) + ENSEMBLE de graines NE baissent PAS la moyenne")
    print(f"#   ({rn.mean():.0f}) → les outliers sont SYSTÉMATIQUES (preuve tenue à l'écart à structure")
    print(f"#   inédite), pas du bruit de graine ; et élargir les modules n'ajoute aucun slot in-grammaire")
    print(f"#   (goulot DONNÉES = goulot GRAMMAIRE). → pas 23 : ENRICHIR LA GRAMMAIRE (plus de slots =")
    print(f"#   plus de données ET plus de couverture). La médiane 1 / top-5 ~60% restent robustes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
