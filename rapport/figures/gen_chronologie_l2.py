# -*- coding: utf-8 -*-
"""Figure : temps de certification noyau des briques du Lemme 2 (ℵ₀·ℵ₀ = ℵ₀).

Temps MESURÉS (pytest, sessions des 21-22 août 2026) de la première
certification de chaque étage de la pile W. Reproductible :
    python rapport/figures/gen_chronologie_l2.py
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BRIQUES = [
    ("W1+W2  parité, cancellation", 44.7),
    ("W3a  pont a^(m+d)=a^m·a^d", 0.13),
    ("W3b  base^n ≠ 0", 2.9),
    ("ops  commut/assoc produit", 0.07),
    ("W3  2-valuation unique (C61)", 38.6),
    ("W4  3-injectivité (C61)", 33.8),
    ("W5  couplage injectif", 90.2),
    ("W6+W7  graphe + Cantor-Bernstein", 173.4),
]

fig, ax = plt.subplots(figsize=(8.2, 3.6))
noms = [n for n, _ in BRIQUES]
mins = [m for _, m in BRIQUES]
y = range(len(BRIQUES))
bars = ax.barh(y, mins, color="#4878a8", height=0.62)
ax.set_yticks(list(y))
ax.set_yticklabels(noms, fontsize=8.5)
ax.invert_yaxis()
ax.set_xlabel("temps de certification noyau (minutes)", fontsize=9)
ax.set_title("Lemme 2 (E III.48) : la pile W du couplage 2^m·3^n — "
             "6,4 h de vérification LCF cumulée", fontsize=9.5)
for b, m in zip(bars, mins):
    ax.text(b.get_width() + 2, b.get_y() + b.get_height() / 2,
            ("%.0f min" % m) if m >= 1 else ("%.0f s" % (m * 60)),
            va="center", fontsize=8)
ax.set_xlim(0, 205)
ax.grid(axis="x", alpha=0.25)
fig.tight_layout()
fig.savefig(__file__.replace("gen_chronologie_l2.py", "chronologie_l2.png"), dpi=160)
print("OK chronologie_l2.png")
