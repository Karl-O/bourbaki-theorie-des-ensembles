"""Tests §III.4.1 — « 0 EST UN ENTIER NATUREL » : ⊢ Fini(0).

Vérifie (conclusion EXACTE + est_clos) :
  • cardinal_vide_egale_vide      ⊢ Card(∅) = ∅            (« 0 = ∅ ») ;
  • successeur_zero_egale_un       ⊢ successeur(0) = Card({∅})  (« 0 + 1 = 1 ») ;
  • zero_distinct_successeur_zero   ⊢ ¬(0 = successeur(0))   (« 0 ≠ 0+1 ») ;
  • zero_est_un_cardinal           ⊢ 0 est un cardinal ;
  • fini_zero                      ⊢ Fini(0)                (0 EST UN ENTIER NATUREL).

Et la FIDÉLITÉ du successeur : successeur(𝔞) EST la somme cardinale binaire
somme_cardinale_binaire(𝔞, {∅}) = Card(𝔞 ⊔ {∅}) (définition de 𝔞+1 de Bourbaki).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, non, et
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, somme_cardinale_binaire
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (cardinal_vide_egale_vide, successeur_zero_egale_un,
                                 zero_distinct_successeur_zero, zero_est_un_cardinal,
                                 fini_zero)

_VIDE = E.VIDE
_ZERO = cardinal(_VIDE)              # 0 = Card(∅)
_SING = E.singleton(_VIDE)           # {∅}
_CARD_SING = cardinal(_SING)         # Card({∅}) = 1


def test_successeur_est_la_somme_cardinale():
    """FIDÉLITÉ : successeur(𝔞) EST somme_cardinale_binaire(𝔞, {∅}) = Card(𝔞 ⊔ {∅}).

    Le successeur n'est plus un terme opaque app("succ",·) ; c'est, par définition,
    la somme cardinale 𝔞 + 1 (Bourbaki E.III.4.1 / III.3.3)."""
    a = var("a")
    assert Ent.successeur(a) == somme_cardinale_binaire(a, _SING)
    assert Ent.successeur(a) == cardinal(somme_disjointe(a, _SING))
    # premiers entiers cohérents
    assert Ent.UN == Ent.successeur(Ent.ZERO)
    assert Ent.ZERO == _ZERO


def test_cardinal_vide_egale_vide():
    """⊢ Card(∅) = ∅ — « 0 = ∅ » (E.III.3.1, Ex. 1), conclusion exacte + clos."""
    thm = cardinal_vide_egale_vide()
    assert thm.est_clos
    assert thm.conclusion == egal(_ZERO, _VIDE)


def test_successeur_zero_egale_un():
    """⊢ successeur(0) = Card({∅}) — « 0 + 1 = 1 », conclusion exacte + clos."""
    thm = successeur_zero_egale_un()
    assert thm.est_clos
    assert thm.conclusion == egal(Ent.successeur(_ZERO), _CARD_SING)


def test_zero_distinct_successeur_zero():
    """⊢ ¬(0 = successeur(0)) — « 0 ≠ 0+1 », conclusion exacte + clos."""
    thm = zero_distinct_successeur_zero()
    assert thm.est_clos
    assert thm.conclusion == non(egal(_ZERO, Ent.successeur(_ZERO)))


def test_zero_est_un_cardinal():
    """⊢ 0 est un cardinal — 1er conjoint de Fini(0), conclusion exacte + clos."""
    thm = zero_est_un_cardinal()
    assert thm.est_clos
    assert thm.conclusion == est_cardinal(_ZERO)


def test_fini_zero():
    """⊢ Fini(0) — 0 EST UN ENTIER NATUREL (E.III.4.1, Déf. 1), conclusion exacte + clos.

    Fini(0) = (0 est un cardinal) ∧ (0 ≠ 0+1) = est_fini(0).  JALON : premier entier
    naturel concret certifié par le noyau."""
    thm = fini_zero()
    assert thm.est_clos
    # Fini(0) EST est_fini(0) = est_fini(Card ∅)  (la Déf. 1 appliquée à 0)
    assert thm.conclusion == Ent.est_fini(_ZERO)
    # et c'est bien la conjonction (cardinal ∧ ≠ succ) — fidélité Déf. 1
    assert thm.conclusion == et(est_cardinal(_ZERO),
                                non(egal(_ZERO, Ent.successeur(_ZERO))))
