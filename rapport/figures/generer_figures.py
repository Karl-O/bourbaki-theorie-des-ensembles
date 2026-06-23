# -*- coding: utf-8 -*-
"""Genere deux figures PNG pour le rapport LaTeX (architecture + memoisation).

Sorties (dpi=150, fond blanc) dans le meme dossier que ce script :
  - architecture_noyau.png : empilement en couches de la chaine de confiance.
  - memoisation_subst.png  : bar chart avant/apres memoisation de subst pure.

Aucune donnee aleatoire ni horodatage : figures reproductibles a l'identique.
"""
import os
import matplotlib
matplotlib.use("Agg")  # backend non interactif
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

DOSSIER = os.path.dirname(os.path.abspath(__file__))
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10})


def figure_architecture(chemin):
    """Schema en couches empilees de l'architecture de confiance.

    Coordonnees en donnees (axes 0..10 x 0..10) pour empiler proprement,
    de bas en haut : noyau, frontiere, tactiques, notions, preuves.
    """
    fig, ax = plt.subplots(figsize=(9.5, 7.0))
    fig.patch.set_facecolor("white")
    ax.set_facecolor("white")
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis("off")

    x0, larg = 0.6, 8.0          # marge droite reservee a l'annotation
    h, ecart = 1.35, 0.25        # hauteur de couche / espace inter-couches

    # Couche (a) : noyau LCF (couleur distincte, plus marquante).
    y = 0.6
    ax.add_patch(Rectangle((x0, y), larg, h, facecolor="#f4a259",
                           edgecolor="#7a3b00", linewidth=2.0))
    ax.text(x0 + larg / 2, y + h / 2,
            "Noyau LCF — primitives N.* (assume, modus_ponens,\n"
            "loi_deduction/C6, generalisation/C27, s1–s7, axiome, instancie)\n"
            "+ verrou _CLE",
            ha="center", va="center", fontsize=10, weight="bold")
    y_noyau = y

    # Annotation : seule la couche (a) produit un Theoreme.
    ax.annotate("Seule cette couche peut\nproduire un objet Theoreme",
                xy=(x0 + larg, y_noyau + h / 2),
                xytext=(x0 + larg + 0.05, y_noyau + h + 0.4),
                ha="left", va="center", fontsize=9.5, color="#b00020",
                weight="bold",
                arrowprops=dict(arrowstyle="->", color="#b00020", lw=1.6),
                annotation_clip=False)

    # Couche (b) : ligne epaisse FRONTIERE DE CONFIANCE, juste au-dessus.
    yf = y + h + ecart
    ax.plot([x0, x0 + larg], [yf, yf], color="#b00020", linewidth=5.0,
            solid_capstyle="round")
    ax.text(x0 + larg / 2, yf + 0.16, "FRONTIÈRE DE CONFIANCE",
            ha="center", va="bottom", fontsize=12, weight="bold",
            color="#b00020")

    # Couches (c)–(e) : tactiques, notions, preuves (au-dessus de la frontiere).
    superieures = [
        ("Tactiques (conjonction, équivalence, quantificateurs, Leibniz…)",
         "#a8d5ba"),
        ("Notions ensemblistes (familles, produits, ordre, équivalence)",
         "#7fb7d6"),
        ("Preuves certifiées du rapport (25 théorèmes ÉTAPE B)", "#c9b6e4"),
    ]
    y = yf + 0.45
    for texte, couleur in superieures:
        ax.add_patch(Rectangle((x0, y), larg, h, facecolor=couleur,
                               edgecolor="#333333", linewidth=1.4))
        ax.text(x0 + larg / 2, y + h / 2, texte, ha="center", va="center",
                fontsize=10.5, weight="bold")
        y += h + ecart

    ax.set_title("Architecture de confiance — empilement des couches",
                 fontsize=14, weight="bold", pad=12)
    ax.text(x0, 0.2, "Aucune dépendance externe — chaîne close et auditée.",
            ha="left", va="top", fontsize=9, style="italic", color="#444444")

    fig.savefig(chemin, dpi=150, facecolor="white", bbox_inches="tight")
    plt.close(fig)


def figure_memoisation(chemin):
    """Bar chart avant/apres memoisation de subst_t/subst_f."""
    avant, apres = 551.0, 397.0
    gain = (avant - apres) / avant * 100.0

    fig, ax = plt.subplots(figsize=(7.0, 6.0))
    fig.patch.set_facecolor("white")
    ax.set_facecolor("white")

    barres = ax.bar(["avant", "après"], [avant, apres],
                    color=["#c44e52", "#4c9f70"], width=0.55,
                    edgecolor="#222222", linewidth=1.2)
    for b, v in zip(barres, [avant, apres]):
        ax.text(b.get_x() + b.get_width() / 2, v + 8, f"{v:.0f} s",
                ha="center", va="bottom", fontsize=12, weight="bold")

    ax.set_ylabel("Temps (secondes)", fontsize=11)
    ax.set_ylim(0, avant * 1.18)
    ax.grid(axis="y", linestyle=":", alpha=0.4)
    ax.set_axisbelow(True)

    fig.suptitle("Mémoïsation de subst_t/subst_f (fonctions pures du noyau)",
                 fontsize=13, weight="bold", y=0.98)
    ax.set_title("le mur algorithmique cardinal subsiste — d'où le pivot vers "
                 "les résultats\nensemblistes/d'ordre", fontsize=9.5,
                 style="italic", color="#444444", pad=10)

    # Annotation du gain en pourcentage.
    ax.annotate(f"gain ≈ {gain:.0f} %", xy=(1, apres),
                xytext=(0.5, (avant + apres) / 2 + 40), ha="center",
                fontsize=12.5, weight="bold", color="#1a6e3c",
                arrowprops=dict(arrowstyle="-|>", color="#1a6e3c", lw=1.8))

    fig.savefig(chemin, dpi=150, facecolor="white", bbox_inches="tight")
    plt.close(fig)


def main():
    p1 = os.path.join(DOSSIER, "architecture_noyau.png")
    p2 = os.path.join(DOSSIER, "memoisation_subst.png")
    figure_architecture(p1)
    figure_memoisation(p2)
    for p in (p1, p2):
        print(f"OK {p} ({os.path.getsize(p)} octets)")


if __name__ == "__main__":
    main()
