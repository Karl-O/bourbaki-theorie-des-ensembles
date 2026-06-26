"""Caractérisation LEIBNIZIENNE de l'égalité par appartenance aux parties.

Résumé E.R.3, n°11 (E.R.3, p.3-12) : « la relation d'égalité "x=y" est
ÉQUIVALENTE à la relation "pour tout X tel que x∈X, on a y∈X" ».  Autrement dit,
x et y sont égaux SI ET SEULEMENT SI ils appartiennent aux mêmes parties.

  ⊢ ( (x = y)  ⇔  (∀X)( (x∈X) ⇒ (y∈X) ) )

THÉORÈME CLOS (0 hypothèse), pur 22-axiomes — AUCUNE théorie dédiée, aucun S8.

Stratégie (les deux sens, déchargés par la loi de déduction C6) :

  ⇒  De x=y, le schéma S6 (Leibniz/substitution) pour le motif Φ(w) = « w∈X »
     donne (x∈X) ⇔ (y∈X), d'où (x∈X) ⇒ (y∈X) ; généralisation sur X (X n'est
     pas libre dans l'hypothèse x=y) ⟹ (∀X)(x∈X⇒y∈X).

  ⇐  C'est le sens FORT : il faut FABRIQUER x=y à partir du quantificateur.  On
     instancie ∀X au TÉMOIN X := {x} (singleton).  Alors :
       • x∈{x} est vrai (appartient_singleton) ;
       • l'hypothèse instanciée donne x∈{x} ⇒ y∈{x}, donc y∈{x} ;
       • y∈{x} ⇔ (y=x) (caractérisation du singleton via l'axiome de la paire +
         idempotence de ∨), d'où y=x, puis x=y par symétrie de =.
     Sans ce témoin, l'énoncé serait une tautologie déguisée ; c'est {x} qui
     force l'égalité.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (var, egal, ou, impl, appartient, equiv, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, equivalence_avant, equivalence_transitivite)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import appartient_singleton


def _membre_singleton(t, a):
    """⊢ (T ∈ {A}) ⇔ (T = A).  ({A} = {A,A} : axiome de la paire + idempotence de ∨.)

    Re-démontré ici avec les seules primitives N.* + l'AXIOME_PAIRE des 22 axiomes
    (la version de ensembles_theoremes est privée) ; aucune théorie dédiée."""
    eq = egal(t, a)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PAIRE)   # (∀x)(∀y)(∀z)(z∈{x,y}⇔(z=x∨z=y))
    inst = instancie(instancie(instancie(ax, a), a), t)    # (T∈{A,A}) ⇔ (T=A ∨ T=A)
    idem = conjonction_intro(N.s1(eq), N.s2(eq, eq))       # (T=A ∨ T=A) ⇔ (T=A)
    return equivalence_transitivite(inst, idem)            # (T∈{A}) ⇔ (T=A)


# @livre Ch.R §1.11 Prop.11 | E.R.3 L.46-49 | PDF p.306
def egalite_leibniz_parties(x="x", y="y"):
    """⊢ ( (x=y) ⇔ (∀X)( (x∈X) ⇒ (y∈X) ) ).  (Résumé E.R.3, n°11 — Leibniz.)

    Théorème CLOS (est_clos == True, 0 hypothèse) ; pur 22-axiomes."""
    vx, vy = var(x), var(y)
    X = var("X")

    # ── sens ⇒ : (x=y) ⇒ (∀X)(x∈X ⇒ y∈X) ───────────────────────────────────────
    h_eg = N.assume(egal(vx, vy))                          # {x=y} ⊢ x=y
    leib = N.s6(vx, vy, "w", appartient(var("w"), X))      # (x=y) ⇒ ((x∈X) ⇔ (y∈X))
    equ = N.modus_ponens(h_eg, leib)                       # {x=y} ⊢ (x∈X) ⇔ (y∈X)
    imp = equivalence_avant(equ)                           # {x=y} ⊢ (x∈X) ⇒ (y∈X)
    gen = N.generalisation("X", imp)                       # {x=y} ⊢ (∀X)(x∈X⇒y∈X)
    sens_avant = N.loi_deduction(egal(vx, vy), gen)        # ⊢ (x=y) ⇒ (∀X)(x∈X⇒y∈X)

    # ── sens ⇐ : (∀X)(x∈X ⇒ y∈X) ⇒ (x=y)  — témoin X := {x} ─────────────────────
    H = pourtout("X", impl(appartient(vx, X), appartient(vy, X)))
    h_H = N.assume(H)                                      # {H} ⊢ (∀X)(x∈X⇒y∈X)
    inst_sx = instancie(h_H, E.singleton(vx))             # {H} ⊢ (x∈{x}) ⇒ (y∈{x})
    x_dans_sx = appartient_singleton(x)                    # ⊢ x∈{x}
    y_dans_sx = N.modus_ponens(x_dans_sx, inst_sx)         # {H} ⊢ y∈{x}
    y_eg_x = N.modus_ponens(y_dans_sx,                     # {H} ⊢ y=x
                            equivalence_avant(_membre_singleton(vy, vx)))
    x_eg_y = N.modus_ponens(y_eg_x, symetrie(vy, vx))      # {H} ⊢ x=y
    sens_arriere = N.loi_deduction(H, x_eg_y)              # ⊢ (∀X)(x∈X⇒y∈X) ⇒ (x=y)

    # ── conjonction des deux sens ⟹ l'équivalence (théorème CLOS) ───────────────
    return conjonction_intro(sens_avant, sens_arriere)     # ⊢ (x=y) ⇔ (∀X)(x∈X⇒y∈X)


__all__ = ["egalite_leibniz_parties"]
