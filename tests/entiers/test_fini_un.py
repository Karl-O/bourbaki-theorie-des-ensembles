"""Tests §III.4.1 — « 1 EST UN ENTIER NATUREL » : ⊢ Fini(1).

Vérifie (conclusion EXACTE + est_clos) :
  • pigeonhole_un_deux            ⊢ ¬Eq({∅}, {∅}⊔{∅})        (« 1 ≠ 2 », tiroirs) ;
  • un_egale_card_singleton       ⊢ 1 = Card({∅})           (« 1 = successeur(0) ») ;
  • eq_un_singleton               ⊢ Eq(1, {∅})              (1 équipotent à {∅}) ;
  • successeur_un_egale_card_deux ⊢ successeur(1) = Card({∅}⊔{∅})  (« 1+1 = 2 ») ;
  • un_distinct_successeur_un      ⊢ ¬(1 = successeur(1))    (« 1 ≠ 1+1 ») ;
  • un_est_un_cardinal            ⊢ 1 est un cardinal ;
  • fini_un                       ⊢ Fini(1)                 (1 EST UN ENTIER NATUREL).
"""
from bourbaki.logique.formule import var, egal, non, et
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_cardinal, equipotent
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (pigeonhole_un_deux, un_egale_card_singleton,
                               eq_un_singleton, successeur_un_egale_card_deux,
                               un_distinct_successeur_un, un_est_un_cardinal, fini_un)

_VIDE = E.VIDE
_SING = E.singleton(_VIDE)               # {∅}
_CARD_SING = cardinal(_SING)             # Card({∅}) = 1
_UN = Ent.UN                             # 1 = successeur(0)
_DEUX_SET = somme_disjointe(_SING, _SING)   # {∅} ⊔ {∅}  (« 2 » ensembliste)


def test_pigeonhole_un_deux():
    """⊢ ¬Eq({∅}, {∅}⊔{∅}) — « 1 ≠ 2 » (principe des tiroirs), conclusion exacte + clos.

    Le singleton {∅} n'est PAS équipotent à la somme disjointe à deux copies {∅}⊔{∅}
    (qui a deux éléments distincts (∅,0), (∅,1)) : une bijection forcerait, via
    fonctionnalité sur le singleton, (∅,0)=(∅,1), donc 0=1, contradiction."""
    thm = pigeonhole_un_deux()
    assert thm.est_clos
    assert thm.conclusion == non(equipotent(_SING, _DEUX_SET))


def test_un_egale_card_singleton():
    """⊢ 1 = Card({∅}) — « 1 = successeur(0) = Card({∅}) », conclusion exacte + clos."""
    thm = un_egale_card_singleton()
    assert thm.est_clos
    assert thm.conclusion == egal(_UN, _CARD_SING)


def test_eq_un_singleton():
    """⊢ Eq(1, {∅}) — 1 = Card({∅}) est équipotent à {∅}, conclusion exacte + clos."""
    thm = eq_un_singleton()
    assert thm.est_clos
    assert thm.conclusion == equipotent(_UN, _SING)


def test_successeur_un_egale_card_deux():
    """⊢ successeur(1) = Card({∅}⊔{∅}) — « 1 + 1 = 2 », conclusion exacte + clos."""
    thm = successeur_un_egale_card_deux()
    assert thm.est_clos
    assert thm.conclusion == egal(Ent.successeur(_UN), cardinal(_DEUX_SET))


def test_un_distinct_successeur_un():
    """⊢ ¬(1 = successeur(1)) — « 1 ≠ 1+1 », conclusion exacte + clos."""
    thm = un_distinct_successeur_un()
    assert thm.est_clos
    assert thm.conclusion == non(egal(_UN, Ent.successeur(_UN)))


def test_un_est_un_cardinal():
    """⊢ 1 est un cardinal — 1er conjoint de Fini(1), conclusion exacte + clos."""
    thm = un_est_un_cardinal()
    assert thm.est_clos
    assert thm.conclusion == est_cardinal(_UN)


def test_fini_un():
    """⊢ Fini(1) — 1 EST UN ENTIER NATUREL (E.III.4.1, Déf. 1), conclusion exacte + clos.

    Fini(1) = (1 est un cardinal) ∧ (1 ≠ 1+1) = est_fini(1).  JALON : 2e entier
    naturel concret certifié par le noyau (via le pigeonhole 1 ≠ 2)."""
    thm = fini_un()
    assert thm.est_clos
    # Fini(1) EST est_fini(1) = est_fini(successeur(0))  (la Déf. 1 appliquée à 1)
    assert thm.conclusion == Ent.est_fini(_UN)
    # et c'est bien la conjonction (cardinal ∧ ≠ succ) — fidélité Déf. 1
    assert thm.conclusion == et(est_cardinal(_UN),
                                non(egal(_UN, Ent.successeur(_UN))))
