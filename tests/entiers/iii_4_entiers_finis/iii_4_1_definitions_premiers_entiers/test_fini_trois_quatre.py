"""Tests — « 3 ET 4 SONT DES ENTIERS NATURELS » :  ⊢ Fini(3), ⊢ Fini(4).

Fini(3) = (3 cardinal) ∧ (3 ≠ 3+1) ; Fini(4) = (4 cardinal) ∧ (4 ≠ 4+1).  Le 2ᵉ
conjoint (3 ≠ 4, puis 4 ≠ 5) repose sur la PROPOSITION 8 (injectivité du successeur,
CAS 2 fermé par la transposition construite), enchaînée depuis deux_distinct_successeur_deux.
On certifie chaque brique + les jalons Fini(3) et Fini(4).
"""
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_trois_quatre import (
    card_trois_egale_trois, card_quatre_egale_quatre,
    trois_distinct_successeur_trois, quatre_distinct_successeur_quatre,
    trois_est_un_cardinal, quatre_est_un_cardinal,
    fini_trois, fini_quatre)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import TROIS, QUATRE, successeur, est_fini, est_cardinal
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.logique.i_1_termes_relations.formule import egal, non


def test_card_trois_egale_trois():
    th = card_trois_egale_trois()
    assert th.est_clos and th.conclusion == egal(cardinal(TROIS), TROIS)


def test_card_quatre_egale_quatre():
    th = card_quatre_egale_quatre()
    assert th.est_clos and th.conclusion == egal(cardinal(QUATRE), QUATRE)


def test_trois_distinct_successeur_trois():
    th = trois_distinct_successeur_trois()
    assert th.est_clos
    assert th.conclusion == non(egal(TROIS, successeur(TROIS)))   # 3 ≠ 3+1  (= 3 ≠ 4)


def test_quatre_distinct_successeur_quatre():
    th = quatre_distinct_successeur_quatre()
    assert th.est_clos
    assert th.conclusion == non(egal(QUATRE, successeur(QUATRE)))  # 4 ≠ 4+1  (= 4 ≠ 5)


def test_trois_est_un_cardinal():
    th = trois_est_un_cardinal()
    assert th.est_clos and th.conclusion == est_cardinal(TROIS)


def test_quatre_est_un_cardinal():
    th = quatre_est_un_cardinal()
    assert th.est_clos and th.conclusion == est_cardinal(QUATRE)


def test_fini_trois():
    th = fini_trois()
    assert th.est_clos
    assert th.conclusion == est_fini(TROIS)              # JALON : 3 EST UN ENTIER NATUREL


def test_fini_quatre():
    th = fini_quatre()
    assert th.est_clos
    assert th.conclusion == est_fini(QUATRE)             # JALON : 4 EST UN ENTIER NATUREL
