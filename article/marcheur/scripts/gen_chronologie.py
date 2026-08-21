# -*- coding: utf-8 -*-
"""Figure : ou passe le temps — quatre recherches sur le MEME but B4.

Chiffres de article/marcheur/MESURES.md (21 aout 2026), recopies ici en
CONSTANTES et REIMPRIMES a l'execution (regle STYLE_ARTICLES §5 : le script
recalcule et imprime ce qu'il trace ; toute divergence avec MESURES.md est
une alarme).

Ce que la figure NE prouve PAS : aucune generalite — un but, un banc, une
machine ; les durees d'echec dependent du budget (max_pas=5, max_noeuds).
"""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# MESURES.md §1 et §4 — 21 aout 2026
DIRECT_ECHEC = 692.54          # chainage seul, ECHOUE
CUMULE = 962.42                # lois brutes + lemme, ferme
COMPRIME_1 = 72.59             # lemme seul, ferme
MARCHE_MINAGE = 4.0            # marche de bout en bout, ferme (414.24 total)
MARCHE_CONJ = 49.2
MARCHE_RETRY = 361.0
MARCHE_TOTAL = 414.24

lignes = [
    ("walk, end to end\n(mine + conjecture + retry)", MARCHE_TOTAL, "walk"),
    ("compressed pool\n(the derived lemma alone)", COMPRIME_1, "ok"),
    ("cumulative pool\n(raw laws + derived lemma)", CUMULE, "ok"),
    ("chaining alone\n(raw laws, budget exhausted)", DIRECT_ECHEC, "echec"),
]

fig, ax = plt.subplots(figsize=(8.6, 3.4))
y = range(len(lignes))
COUL = {"ok": "#5b8dbf", "echec": "#c25b4e", "walk": "#4e9a6f"}

for i, (nom, duree, genre) in enumerate(lignes):
    if genre == "walk":
        ax.barh(i, MARCHE_MINAGE, color="#2e6e4b", height=0.55)
        ax.barh(i, MARCHE_CONJ, left=MARCHE_MINAGE, color="#7fbf9b",
                height=0.55)
        ax.barh(i, MARCHE_RETRY, left=MARCHE_MINAGE + MARCHE_CONJ,
                color=COUL["walk"], height=0.55)
        ax.text(MARCHE_TOTAL + 12, i, "414 s — CLOSED", va="center",
                fontsize=10, fontweight="bold", color="#2e6e4b")
        ax.text(MARCHE_MINAGE + MARCHE_CONJ / 2, i + 0.42,
                "mine 4 s + conjecture/certify 49 s", ha="left", fontsize=8,
                color="#2e6e4b")
        ax.text(MARCHE_MINAGE + MARCHE_CONJ + MARCHE_RETRY / 2, i,
                "retry on 2 lemmas: 361 s", ha="center", va="center",
                fontsize=8.5, color="white")
    else:
        ax.barh(i, duree, color=COUL[genre], height=0.55)
        etiquette = ("%.0f s — FAILS (1 gap named)" % duree
                     if genre == "echec" else "%.0f s — closed" % duree)
        coul = "#c25b4e" if genre == "echec" else "#3a6389"
        ax.text(duree + 12, i, etiquette, va="center", fontsize=10,
                fontweight=("bold" if genre == "echec" else "normal"),
                color=coul)

ax.set_yticks(list(y))
ax.set_yticklabels([n for n, _, _ in lignes], fontsize=9)
ax.set_xlabel("wall-clock seconds — same goal $B_4$, same budgets, one machine",
              fontsize=9)
ax.set_xlim(0, 1210)
ax.spines[["top", "right"]].set_visible(False)
ax.grid(axis="x", alpha=0.25, linewidth=0.6)
ax.set_axisbelow(True)
fig.tight_layout()
sortie = __file__.replace("gen_chronologie.py", "../chronologie.png")
fig.savefig(sortie, dpi=160)

print("trace :")
for nom, duree, genre in lignes:
    print("  %-48s %8.2f s  %s" % (nom.replace("\n", " "), duree, genre))
print("somme marche = %.2f (minage %.1f + conj %.1f + retry %.1f = %.1f)"
      % (MARCHE_TOTAL, MARCHE_MINAGE, MARCHE_CONJ, MARCHE_RETRY,
         MARCHE_MINAGE + MARCHE_CONJ + MARCHE_RETRY))
print("ecrit :", sortie)
