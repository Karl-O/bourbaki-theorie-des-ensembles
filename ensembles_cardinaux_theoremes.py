"""§III.3 — Cardinaux : Proposition 1 (Eq(X,Y) ⇔ Card X = Card Y).

Repose sur : l'équipotence est une relation d'ÉQUIVALENCE (réflexive +
symétrique + transitive, prouvées dans ensembles_equipotence/ensembles_bijection),
l'identité Eq(X, Card X) (via existe_temoin sur Card X = τ_Z Eq(X,Z)), et le
schéma S7 (congruence de τ sous équivalence universelle).
"""
from __future__ import annotations

from formule import var, egal
import noyau_abrege as N
import ensembles_abrege as E
from tactiques_abrege2 import (conjonction_intro, equivalence_avant, instancie)
from ensembles_cardinaux import equipotent, cardinal, est_injection_de, inf_egal_card
from ensembles_equipotence import (equipotence_reflexive, diagonale_fonctionnelle,
                                   diagonale_domaine, diagonale_injective, diagonale_image)
from ensembles_bijection import equipotence_symetrique, equipotence_transitive
from tactiques_abrege import inclusion_reflexive
from tactiques_abrege2 import equivalence_arriere
from formule import inclus


def _sym_all():
    """⊢ (∀X)(∀Y)(Eq(X,Y) ⇒ Eq(Y,X))."""
    return N.generalisation("X", N.generalisation("Y", equipotence_symetrique("F", "X", "Y")))


def _trans_all():
    """⊢ (∀X)(∀Y)(∀Z)((Eq(X,Y) et Eq(Y,Z)) ⇒ Eq(X,Z))."""
    return N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        equipotence_transitive("F", "G", "X", "Y", "Z"))))


def equipotent_son_cardinal(x="X"):
    """⊢ Eq(X, Card X).   (tout ensemble est équipotent à son cardinal, via existe_temoin.)"""
    vX = var(x)
    R = equipotent(vX, var("Z"))                                 # Eq(X, Z)
    ex = N.modus_ponens(equipotence_reflexive(x), N.s5(R, vX, "Z"))   # (∃Z) Eq(X,Z)
    return N.modus_ponens(ex, N.existe_temoin(R, "Z"))          # Eq(X, τ_Z Eq(X,Z)) = Eq(X, Card X)


def cardinal_egal_si_equipotent(x="X", y="Y"):
    """⊢ Eq(X, Y) ⇒ (Card X = Card Y).   (Proposition 1, SENS DIRECT, E.III.3.1.)

    Sens direct certifié via S7 : Eq(X,Y) entraîne (∀Z)(Eq(X,Z)⇔Eq(Y,Z)) [symétrie +
    transitivité], d'où τ_Z(Eq(X,Z))=τ_Z(Eq(Y,Z)), c.-à-d. Card X=Card Y.  On utilise
    les théorèmes d'équipotence DIRECTEMENT (noms de variables, pas d'instanciation)."""
    vX, vY, vZ = var(x), var(y), var("Z")
    hxy = N.assume(equipotent(vX, vY))
    eq_yx = N.modus_ponens(hxy, equipotence_symetrique("F", x, y))      # Eq(Y,X)
    fwd_in = N.loi_deduction(equipotent(vX, vZ), N.modus_ponens(
        conjonction_intro(eq_yx, N.assume(equipotent(vX, vZ))),
        equipotence_transitive("F", "G", y, x, "Z")))                  # Eq(X,Z)⇒Eq(Y,Z)
    bwd_in = N.loi_deduction(equipotent(vY, vZ), N.modus_ponens(
        conjonction_intro(hxy, N.assume(equipotent(vY, vZ))),
        equipotence_transitive("F", "G", x, y, "Z")))                  # Eq(Y,Z)⇒Eq(X,Z)
    gen_Z = N.generalisation("Z", conjonction_intro(fwd_in, bwd_in))    # (∀Z)(Eq(X,Z)⇔Eq(Y,Z))
    card_eq = N.modus_ponens(gen_Z, N.s7(equipotent(vX, vZ), equipotent(vY, vZ), "Z"))  # Card X=Card Y
    return N.loi_deduction(equipotent(vX, vY), card_eq)


def equipotent_si_cardinal_egal(x="X", y="Y"):
    """⊢ (Card X = Card Y) ⇒ Eq(X, Y).   (Proposition 1, SENS RÉCIPROQUE, E.III.3.1.)

    Card X=Card Y, Eq(X,Card X) [existe_temoin] et Card X=Card Y donnent Eq(X,Card Y) ;
    Eq(Y,Card Y) + symétrie donne Eq(Card Y,Y) ; transitivité conclut Eq(X,Y).
    (Débloqué par le renommage DÉTERMINISTE de _fraiche : symétrie applicable au
    terme Card Y via instancie sans casser le matching.)"""
    vX, vY = var(x), var(y)
    sym, trans = _sym_all(), _trans_all()
    eX, eY = equipotent_son_cardinal(x), equipotent_son_cardinal(y)
    cX, cY = cardinal(vX), cardinal(vY)
    hcard = N.assume(egal(cX, cY))
    eX_cY = N.modus_ponens(eX, equivalence_avant(N.modus_ponens(
        hcard, N.s6(cX, cY, "w", equipotent(vX, var("w"))))))          # Eq(X, Card Y)
    eq_cY_Y = N.modus_ponens(eY, instancie(instancie(sym, vY), cY))    # Eq(Card Y, Y)
    tr = instancie(instancie(instancie(trans, vX), cY), vY)            # (Eq(X,CardY) et Eq(CardY,Y))⇒Eq(X,Y)
    exy = N.modus_ponens(conjonction_intro(eX_cY, eq_cY_Y), tr)        # Eq(X,Y)
    return N.loi_deduction(egal(cX, cY), exy)


def proposition_1_cardinaux(x="X", y="Y"):
    """⊢ Eq(X, Y) ⇔ (Card X = Card Y).   (Proposition 1 COMPLÈTE, E.III.3.1.)"""
    return conjonction_intro(cardinal_egal_si_equipotent(x, y),
                             equipotent_si_cardinal_egal(x, y))


def inf_egal_reflexif(x="X"):
    """⊢ X ≤ X   (réflexivité de l'ordre des cardinaux : l'identité Δ_X injecte X dans X)."""
    vX = var(x)
    DX = E.diagonale(vX)
    incl_img = N.modus_ponens(inclusion_reflexive(x), equivalence_arriere(N.modus_ponens(
        diagonale_image(x), N.s6(E.image(DX, vX), vX, "w", inclus(var("w"), vX)))))  # image(Δ_X,X)⊂X
    inj = conjonction_intro(conjonction_intro(conjonction_intro(
        diagonale_fonctionnelle(x), diagonale_domaine(x)), diagonale_injective(x)), incl_img)
    return N.modus_ponens(inj, N.s5(est_injection_de(var("F"), vX, vX), DX, "F"))  # X ≤ X


def cardinal_inf_egal_reflexif(x="X"):
    """⊢ Card X ≤ Card X   (réflexivité de ≤ sur les cardinaux ; instance-terme via Card X)."""
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))         # (∀X)(X ≤ X)
    return instancie(refl_all, cardinal(var(x)))                    # Card X ≤ Card X


__all__ = ["equipotent_son_cardinal", "cardinal_egal_si_equipotent",
           "equipotent_si_cardinal_egal", "proposition_1_cardinaux"]
