"""§III.3.5 — Cantor au niveau CARDINAL : Card X < 2^Card X  (E.III.3, Théorème 2).

Le THÉORÈME 2 de Cantor restaté sur les cardinaux :

    Card X < 2^Card X  :=  ( Card X ≤ 2^Card X )  et  ( Card X ≠ 2^Card X ),

avec 2^Card X = exposant_cardinal_binaire(2, X).  Le PONT set→cardinal est
ENTIÈREMENT outillé : on s'appuie sur le PIVOT cP12 (Proposition 12, CLOS) :

    cP12 :  Card(𝔓X) = exposant_cardinal_binaire(2, X) = 2^Card X
            (card_parties_egale_deux_exp, _bijection).

FACE A — Card X ≤ 2^Card X.  Chaîne de transitivité de ≤ par invariance par
équipotence (Prop 1, Eq(X,Card X)) :
        Card X  ≤  X  ≤  𝔓X  ≤  Card 𝔓X
via `_card_le_set_t` (Card X ≤ X), `inf_egal_parties` (X ≤ 𝔓X, l'injection x↦{x}
de Cantor étape 1) et `_set_le_card_t` (𝔓X ≤ Card 𝔓X) ; puis on réécrit
Card 𝔓X → 2^Card X par Leibniz (S6) avec cP12.

FACE B — Card X ≠ 2^Card X.  `cantor_non_equipotent` donne ¬Eq(X, 𝔓X) (argument
diagonal, E.III.3) ; la Proposition 1 (sens RÉCIPROQUE, version TERME)
(Card X = Card 𝔓X) ⇒ Eq(X, 𝔓X) se CONTRAPOSE en ¬Eq(X,𝔓X) ⇒ ¬(Card X = Card 𝔓X),
d'où ¬(Card X = Card 𝔓X) ; on réécrit Card 𝔓X → 2^Card X sous la négation
(S6 + equiv_neg) avec cP12.

FINAL — conjonction_intro(FACE A, FACE B) = inf_strict_card(Card X, 2^Card X).

Les trois helpers set→cardinal `_card_le_set_t / _set_le_card_t / _le_trans_t`
sont RECOPIÉS LOCALEMENT (patron de
ensembles_hessenberg_structural_discharge) pour éviter d'importer Hessenberg
(dépendance remontante lourde).  INVARIANT : theorie_ensembles() = 22 ; tout vient
de théorèmes déjà prouvés, rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, non
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, instancie, contraposition, equiv_neg)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card, inf_strict_card)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═══════════════════════════════════════════════════════════════════════════════
# HELPERS set→cardinal  (recopiés du patron Hessenberg ; évitent l'import lourd)
# ═══════════════════════════════════════════════════════════════════════════════
def _eq_implique_le_t(tX, tY):
    """⊢ equipotent(X, Y) ⇒ inf_egal_card(X, Y)  pour des TERMES X, Y (CLOS).

    Une bijection est une injection : généralise equipotent_implique_inf_egal
    (CLOS) en X, Y puis instancie aux termes."""
    from bourbaki.cardinaux.iii_4_ordinal_cardinal.realisation_segment.ensembles_subset_realise_close import (
        equipotent_implique_inf_egal)
    gen = N.generalisation("X", N.generalisation("Y",
        equipotent_implique_inf_egal("X", "Y")))
    return instancie(instancie(gen, _t(tX)), _t(tY))


def _card_le_set_t(tX):
    """⊢ inf_egal_card(Card X, X).   (Card X ≤ X via Eq(X, Card X) + symétrie.)

    Eq(X, Card X) (Prop 1, equipotent_son_cardinal) ; symétrie ⇒ Eq(Card X, X) ;
    une bijection est une injection ⇒ Card X ≤ X.  CLOS, 0 hyp ; theorie=22."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_son_cardinal)
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import (
        equipotence_symetrique)
    vX = _t(tX)
    cX = cardinal(vX)
    # Eq(X, Card X) instanciée au terme X
    eq_x_cx = instancie(N.generalisation("X", equipotent_son_cardinal("X")), vX)
    # symétrie : Eq(X, Card X) ⇒ Eq(Card X, X)  (instanciée aux termes X, Card X)
    sym = instancie(instancie(N.generalisation("X", N.generalisation("Y",
        equipotence_symetrique("F", "X", "Y"))), vX), cX)
    eq_cx_x = N.modus_ponens(eq_x_cx, sym)                       # Eq(Card X, X)
    return N.modus_ponens(eq_cx_x, _eq_implique_le_t(cX, vX))    # Card X ≤ X


def _set_le_card_t(tX):
    """⊢ inf_egal_card(X, Card X).   (X ≤ Card X via Eq(X, Card X).)

    Eq(X, Card X) (equipotent_son_cardinal) ; une bijection est une injection ⇒
    X ≤ Card X.  CLOS, 0 hyp ; theorie=22."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_son_cardinal)
    vX = _t(tX)
    cX = cardinal(vX)
    eq_x_cx = instancie(N.generalisation("X", equipotent_son_cardinal("X")), vX)  # Eq(X, Card X)
    return N.modus_ponens(eq_x_cx, _eq_implique_le_t(vX, cX))    # X ≤ Card X


def _le_trans_t(tX, tY, tZ):
    """⊢ (X≤Y et Y≤Z) ⇒ X≤Z  pour des TERMES (transitivité de ≤, instanciée)."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
        inf_egal_transitive_general)
    g = inf_egal_transitive_general("Xt", "Yt", "Zt")
    return instancie(instancie(instancie(g, _t(tX)), _t(tY)), _t(tZ))


def _prop1_reverse_t(tX, tY):
    """⊢ (Card X = Card Y) ⇒ equipotent(X, Y)  pour des TERMES X, Y (Prop 1 réciproque).

    Version TERME du sens réciproque de la Proposition 1
    (equipotent_si_cardinal_egal n'accepte que des NOMS) : généralise en X, Y puis
    instancie aux termes."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
        equipotent_si_cardinal_egal)
    gen = N.generalisation("X", N.generalisation("Y",
        equipotent_si_cardinal_egal("X", "Y")))      # (∀X)(∀Y)(Card X=Card Y ⇒ Eq(X,Y))
    return instancie(instancie(gen, _t(tX)), _t(tY))


# ═══════════════════════════════════════════════════════════════════════════════
# FACE A — Card X ≤ 2^Card X   (chaîne Card X ≤ X ≤ 𝔓X ≤ Card 𝔓X, puis cP12)
# ═══════════════════════════════════════════════════════════════════════════════
def cantor_face_inf_egal(x="X"):
    """⊢ inf_egal_card(Card X, 2^Card X).   (FACE A du Théorème 2 : Card X ≤ 2^Card X.)

    Chaîne de transitivité de ≤ par invariance par équipotence (Prop 1) :
        Card X ≤ X ≤ 𝔓X ≤ Card 𝔓X
    (_card_le_set_t, inf_egal_parties (x↦{x}, Cantor étape 1), _set_le_card_t),
    puis réécriture Card 𝔓X → 2^Card X par Leibniz (S6) avec cP12 (Proposition 12).
    CLOS, 0 hyp ; conclusion ∉ hyps ; theorie=22."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import inf_egal_parties
    from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop12_powerset.ensembles_powerset_exp import deux
    from ._bijection import card_parties_egale_deux_exp
    vX = _t(x)
    PX = E.parties(vX)
    cX, cPX = cardinal(vX), cardinal(PX)
    deux2X = exposant_cardinal_binaire(deux(), vX)
    cible = inf_egal_card(cX, deux2X)
    # Card X ≤ X
    cX_le_X = _card_le_set_t(vX)
    # X ≤ 𝔓X  (injection x↦{x} de Cantor, étape 1 — niveau ENSEMBLES)
    X_le_PX = inf_egal_parties(x)
    # 𝔓X ≤ Card 𝔓X
    PX_le_cPX = _set_le_card_t(PX)
    # Card X ≤ X ≤ 𝔓X : transitivité
    cX_le_PX = N.modus_ponens(conjonction_intro(cX_le_X, X_le_PX),
                              _le_trans_t(cX, vX, PX))            # Card X ≤ 𝔓X
    # Card X ≤ 𝔓X ≤ Card 𝔓X : transitivité
    cX_le_cPX = N.modus_ponens(conjonction_intro(cX_le_PX, PX_le_cPX),
                               _le_trans_t(cX, PX, cPX))         # Card X ≤ Card 𝔓X
    # cP12 : Card 𝔓X = 2^Card X  ;  réécrire le 2e argument de ≤ (Leibniz S6, trou w)
    cP12 = card_parties_egale_deux_exp(x)                        # Card 𝔓X = 2^Card X
    leib = N.s6(cPX, deux2X, "w", inf_egal_card(cX, var("w")))   # (Card𝔓X=2^CardX)⇒(Card X≤Card𝔓X ⇔ Card X≤2^CardX)
    res = N.modus_ponens(cX_le_cPX, equivalence_avant(N.modus_ponens(cP12, leib)))
    assert res.conclusion == cible, \
        f"cantor_face_inf_egal : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "cantor_face_inf_egal : VACUOUS"
    return res


# ═══════════════════════════════════════════════════════════════════════════════
# FACE B — Card X ≠ 2^Card X   (¬Eq(X,𝔓X) + Prop 1 réciproque contraposée, puis cP12)
# ═══════════════════════════════════════════════════════════════════════════════
def cantor_face_non_egal(x="X"):
    """⊢ ¬(Card X = 2^Card X).   (FACE B du Théorème 2 : Card X ≠ 2^Card X.)

    cantor_non_equipotent donne ¬Eq(X, 𝔓X) (argument diagonal, E.III.3) ; la
    Proposition 1 (sens réciproque, version TERME) (Card X = Card 𝔓X) ⇒ Eq(X, 𝔓X)
    se CONTRAPOSE en ¬Eq(X,𝔓X) ⇒ ¬(Card X = Card 𝔓X), d'où ¬(Card X = Card 𝔓X) ;
    on réécrit Card 𝔓X → 2^Card X sous la négation (S6 + equiv_neg) avec cP12.
    CLOS, 0 hyp ; conclusion ∉ hyps ; theorie=22."""
    from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import cantor_non_equipotent
    from ._bijection import card_parties_egale_deux_exp
    from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop12_powerset.ensembles_powerset_exp import deux
    vX = _t(x)
    PX = E.parties(vX)
    cX, cPX = cardinal(vX), cardinal(PX)
    deux2X = exposant_cardinal_binaire(deux(), vX)
    cible = non(egal(cX, deux2X))
    # ¬Eq(X, 𝔓X)
    notEq = cantor_non_equipotent(x)                            # ¬Eq(X, 𝔓X)
    # Prop 1 réciproque : (Card X = Card 𝔓X) ⇒ Eq(X, 𝔓X) ; contraposée
    rev = _prop1_reverse_t(vX, PX)                              # (Card X=Card𝔓X) ⇒ Eq(X,𝔓X)
    contra = contraposition(rev)                                # ¬Eq(X,𝔓X) ⇒ ¬(Card X=Card𝔓X)
    not_card_eq = N.modus_ponens(notEq, contra)                 # ¬(Card X = Card 𝔓X)
    # cP12 : Card 𝔓X = 2^Card X  ;  réécrire sous la négation (S6 + equiv_neg)
    cP12 = card_parties_egale_deux_exp(x)                       # Card 𝔓X = 2^Card X
    leib = N.s6(cPX, deux2X, "w", egal(cX, var("w")))          # (Card𝔓X=2^CardX)⇒(Card X=Card𝔓X ⇔ Card X=2^CardX)
    eq_pos = N.modus_ponens(cP12, leib)                         # (Card X=Card𝔓X) ⇔ (Card X=2^CardX)
    eq_neg = equiv_neg(eq_pos)                                  # ¬(Card X=Card𝔓X) ⇔ ¬(Card X=2^CardX)
    res = N.modus_ponens(not_card_eq, equivalence_avant(eq_neg))   # ¬(Card X = 2^Card X)
    assert res.conclusion == cible, \
        f"cantor_face_non_egal : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "cantor_face_non_egal : VACUOUS"
    return res


# ═══════════════════════════════════════════════════════════════════════════════
# THÉORÈME 2 — Card X < 2^Card X   (Cantor restaté au niveau CARDINAL, E.III.3)
# ═══════════════════════════════════════════════════════════════════════════════
def cantor_deux_exp(x="X"):
    """⊢ Card X < 2^Card X.   (THÉORÈME 2 de Cantor, E.III.3 : 2^a > a, niveau CARDINAL.)

    inf_strict_card(Card X, 2^Card X) := (Card X ≤ 2^Card X) et (Card X ≠ 2^Card X).
    FACE A (cantor_face_inf_egal) : Card X ≤ 2^Card X par la chaîne
    Card X ≤ X ≤ 𝔓X ≤ Card 𝔓X = 2^Card X (cP12, Proposition 12).
    FACE B (cantor_face_non_egal) : Card X ≠ 2^Card X par ¬Eq(X,𝔓X) (argument
    diagonal) + Proposition 1 réciproque contraposée + cP12.
    CLOS, 0 hyp ; conclusion ∉ hyps ; theorie=22."""
    vX = _t(x)
    from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop12_powerset.ensembles_powerset_exp import deux
    cible = inf_strict_card(cardinal(vX), exposant_cardinal_binaire(deux(), vX))
    faceA = cantor_face_inf_egal(x)                            # Card X ≤ 2^Card X
    faceB = cantor_face_non_egal(x)                            # Card X ≠ 2^Card X
    res = conjonction_intro(faceA, faceB)                     # Card X < 2^Card X
    assert res.conclusion == cible, \
        f"cantor_deux_exp : conclusion inattendue\n{res.conclusion}\nvs\n{cible}"
    assert res.conclusion not in res.hypotheses, "cantor_deux_exp : VACUOUS"
    return res


__all__ = ["cantor_face_inf_egal", "cantor_face_non_egal", "cantor_deux_exp"]
