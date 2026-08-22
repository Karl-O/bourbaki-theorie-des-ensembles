# -*- coding: utf-8 -*-
"""Figure : pile de dépendances du chantier R' (C60, récursion transfinie VÉRITABLE).

Jalons R1'-R5' du sous-chantier rec_veritable/ (22 août 2026) : chaque boîte
donne l'énoncé court du jalon et son nombre d'hypothèses honnêtes ; les flèches
sont les dépendances de preuve réelles (imports vérifiés en code). Boîtes
pleines = clos ; pointillés = front R6'-R7' en cours. Reproductible :
    python rapport/figures/gen_chantier_recursion.py
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

BLEU = "#4878a8"        # jalon clos (théorèmes)
BLEU_CLAIR = "#8fb0cc"  # définition / formule pure (aucun théorème)
BLANC = "#ffffff"       # front en cours

# (clé, x, y, largeur, hauteur, couleur, lignes de texte)
BOITES = {
    "R1": (3.4, 0.25, 3.2, 1.05, BLEU_CLAIR,
           ["R1'  est_essai_rec (définition)",
            "p(z) = T{p|seg z} sur TOUT dom p",
            "formule pure — 0 axiome, 0 théorème"]),
    "R2": (0.4, 1.95, 4.0, 1.05, BLEU,
           ["R2'  UNICITÉ  [6 hyp]",
            "essais p, q en x  ⊢  p = q",
            "C59 gardé-par-domaine + congruence C44"]),
    "R3": (5.6, 1.95, 4.0, 1.05, BLEU,
           ["R3'  PROLONGEMENT D'UN PAS  [5 hyp]",
            "essai-sur-seg p  ⊢  p ∪ {(x, T{p})}",
            "essai récursif en x"]),
    "R4": (0.4, 3.65, 4.0, 1.05, BLEU,
           ["R4'  DESCENTE  [3 hyp]  (+compo [1 hyp])",
            "essai p en x, y∈D(x)  ⊢",
            "p|D(y) essai récursif en y"]),
    "R5a": (0.4, 5.35, 4.0, 1.05, BLEU,
            ["R5'a  COÏNCIDENCE sans wlog  [6 hyp]",
             "essais en y, y', point commun a",
             "⊢ p(a) = q(a)  (descente bilatérale)"]),
    "R5b": (5.6, 5.35, 4.0, 1.05, BLEU_CLAIR,
            ["R5'b  FAMILLE S8  Dfam_rec(G,E,x,V)",
             "{p∈P(E×V) | ∃y<x, essai(p,y)}",
             "le terme PORTE le graphe G"]),
    "R5c": (2.6, 7.05, 4.8, 1.05, BLEU,
            ["R5'c  RÉUNION ⋃D  — l'essai-limite",
             "compatible [1] · dom = seg x [2]",
             "équation-restriction [2]"]),
    "R67": (2.6, 8.75, 4.8, 0.95, BLANC,
            ["R6'-R7'  EN COURS",
             "hérédité + couverture C59 + capstone",
             "∃!f sur E,  f(x) = T{f|seg x}"]),
}

FLECHES = [  # (source, cible, pointillé, rad, cote) — rad>0 bombe à gauche du trajet
    ("R1", "R2", False, 0.06, "haut"), ("R1", "R3", False, 0.06, "haut"),
    ("R2", "R4", False, 0.0, "haut"), ("R1", "R5b", False, -0.22, "haut"),
    ("R4", "R5a", False, 0.0, "haut"), ("R2", "R5a", False, 0.30, "gauche"),
    ("R5a", "R5c", False, 0.06, "haut"), ("R5b", "R5c", False, 0.06, "haut"),
    ("R3", "R5c", False, 0.30, "haut"),
    ("R5c", "R67", True, 0.0, "haut"), ("R3", "R67", True, -0.30, "haut"),
]


def _ancre(cle, bord):
    x, y, w, h, _, _ = BOITES[cle]
    if bord == "haut":
        return (x + w / 2, y + h)
    if bord == "bas":
        return (x + w / 2, y)
    return (x, y + h / 2)                                   # gauche


fig, ax = plt.subplots(figsize=(8.6, 6.4))
ax.set_xlim(-0.7, 10)
ax.set_ylim(0, 10.1)
ax.axis("off")

for cle, (x, y, w, h, coul, lignes) in BOITES.items():
    en_cours = coul == BLANC
    boite = FancyBboxPatch(
        (x, y), w, h, boxstyle="round,pad=0.06",
        facecolor=coul, edgecolor="#2b4a66",
        linestyle=":" if en_cours else "-", linewidth=1.2)
    ax.add_patch(boite)
    fonce = coul == BLEU
    for i, ligne in enumerate(lignes):
        ax.text(x + w / 2, y + h - 0.24 - i * 0.32, ligne,
                ha="center", va="center", fontsize=7.4,
                fontweight="bold" if i == 0 else "normal",
                color="white" if fonce else "#1c3247")

for src, dst, pointille, rad, cote in FLECHES:
    if cote == "gauche":                                    # contournement par l'ouest
        x0, y0 = _ancre(src, "gauche")
        x1, y1 = _ancre(dst, "gauche")
        depart, arrivee = (x0 - 0.08, y0), (x1 - 0.08, y1)
    else:
        x0, y0 = _ancre(src, "haut")
        x1, y1 = _ancre(dst, "bas")
        depart, arrivee = (x0, y0 + 0.07), (x1, y1 - 0.10)
    ax.add_patch(FancyArrowPatch(
        depart, arrivee,
        arrowstyle="-|>", mutation_scale=11, linewidth=1.0,
        linestyle=(0, (3, 3)) if pointille else "-",
        color="#5b7a94",
        connectionstyle="arc3,rad=%.2f" % rad, shrinkA=2, shrinkB=2))

ax.set_title("Chantier R' (C60, E III.18-19) : la vraie récursion "
             "p(z) = T{p|seg z} — pile des jalons R1'→R5' (clos)",
             fontsize=9.5)
fig.tight_layout()
fig.savefig(__file__.replace("gen_chantier_recursion.py",
                             "chantier_recursion.png"), dpi=160)
print("OK chantier_recursion.png")
