# -*- coding: utf-8 -*-
"""Figure : pourquoi le COMPTAGE BRUT ne peut pas démontrer Goldbach.

🎯 CE QUE LA FIGURE MONTRE. Deux courbes qui vont en sens contraire :
  · la densité `π(2k)/k` — ce que voit un argument de cardinalité — S'EFFONDRE ;
  · le nombre RÉEL de décompositions de `2k` en somme de deux premiers CROÎT.

Le critère des tiroirs `2·π(2k) > 2k+1` forcerait `P_2k` et son miroir à se
rencontrer par la seule cardinalité. Il ne tient pour AUCUN `k ≥ 2`, et l'écart
se creuse. Pourtant les décompositions abondent. Conclusion : l'information qui
manque porte sur la RÉPARTITION des premiers, pas sur leur nombre.

C'est la version graphique du §6 de l'article, et elle rend visible en un coup
d'œil ce que deux phrases de prose peinaient à faire passer.

⚠️ CETTE FIGURE NE DÉMONTRE RIEN. C'est une mesure numérique sur une plage
finie, calculée par crible, pas un théorème du noyau. L'article le dit ; la
légende le redit. Aucune de ces valeurs n'entre dans une preuve.

Reproduction :
    python article/goldbach/figures/gen_comptage.py
"""
from __future__ import annotations

from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

BORNE = 200_000


def crible(n):
    """Crible d'Ératosthène — rend le tableau de primalité jusqu'à `n` inclus."""
    est = bytearray([1]) * (n + 1)
    est[0] = est[1] = 0
    p = 2
    while p * p <= n:
        if est[p]:
            est[p * p::p] = bytearray(len(est[p * p::p]))
        p += 1
    return est


def mesures(borne=BORNE):
    """Pour une grille de `2k`, rend (2k, densité π(2k)/k, nb de décompositions)."""
    est = crible(borne)
    premiers = [i for i in range(borne + 1) if est[i]]
    #: π(x) cumulé, lu par bisection sur `premiers`
    from bisect import bisect_right
    #: grille LOG-RÉGULIÈRE de 4 à `borne` — une grille en deux morceaux laisse
    #: un trou visible dans la courbe (mesuré : coupure entre 2k=25 et 2k=100).
    grille, x, pas = [], 4, 1.06
    while x <= borne:
        v = 2 * (int(x) // 2)
        if v >= 4 and (not grille or v > grille[-1]):
            grille.append(v)
        x *= pas
    xs, dens, decomp = [], [], []
    for deux_k in grille:
        k = deux_k // 2
        pi = bisect_right(premiers, deux_k)
        n = sum(1 for p in premiers
                if p <= k and est[deux_k - p])          # p ≤ q, pas de doublon
        xs.append(deux_k)
        dens.append(pi / k)
        decomp.append(n)
    return xs, dens, decomp


def figure(chemin):
    xs, dens, decomp = mesures()
    fig, ax = plt.subplots(figsize=(7.2, 3.5))
    ax.plot(xs, dens, color="#b03030", lw=1.6,
            label=r"densité vue par le comptage : $\pi(2k)\,/\,k$")
    ax.axhline(1.0, color="#b03030", ls=":", lw=1.1)
    #: annotation calée à GAUCHE : à droite elle chevauche la courbe bleue.
    ax.text(xs[0] * 1.4, 1.04, r"seuil des tiroirs : $2\,\pi(2k) > 2k+1$"
            "\n" r"— jamais atteint pour $k \geq 2$",
            ha="left", va="bottom", fontsize=8, color="#b03030")
    ax.set_xscale("log")
    ax.set_xlabel(r"$2k$ (échelle logarithmique)")
    ax.set_ylabel(r"$\pi(2k)/k$", color="#b03030")
    ax.tick_params(axis="y", labelcolor="#b03030")
    ax.set_ylim(0, 1.25)

    ax2 = ax.twinx()
    ax2.plot(xs, decomp, color="#20507a", lw=1.6,
             label="décompositions réelles de $2k$")
    ax2.set_yscale("log")
    ax2.set_ylabel("nombre de décompositions de $2k$", color="#20507a")
    ax2.tick_params(axis="y", labelcolor="#20507a")

    #: légende SOUS les axes — placée dedans, elle recouvrait la courbe rouge
    #: entre 2k=25 et 2k=100 et donnait l'illusion d'un trou dans les données.
    lignes = ax.get_lines()[:1] + ax2.get_lines()
    ax.legend(lignes, [l.get_label() for l in lignes],
              loc="upper center", bbox_to_anchor=(.5, -.22), ncol=2,
              fontsize=8, frameon=False)
    ax.set_title("Le comptage regarde la mauvaise quantité", fontsize=10)
    fig.tight_layout()
    fig.savefig(chemin, dpi=200, bbox_inches="tight")
    print("écrit : %s" % chemin)
    print("  plage      2k = %d → %d" % (xs[0], xs[-1]))
    print("  densité    %.3f → %.3f" % (dens[0], dens[-1]))
    print("  décomp.    %d → %d  (paires NON ordonnées, p ≤ q)"
          % (decomp[0], decomp[-1]))
    print("  seuil des tiroirs jamais atteint pour k ≥ 2 : %s"
          % (not any(d > 1.0 for d in dens[1:])))


if __name__ == "__main__":
    figure(Path(__file__).with_name("comptage.png"))
