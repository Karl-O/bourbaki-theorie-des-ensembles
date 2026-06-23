"""Tests — « 2 EST UN ENTIER NATUREL » :  ⊢ Fini(2).  Le JALON.

Fini(2) = (2 cardinal) ∧ (2 ≠ 2+1).  Le 2ᵉ conjoint (2 ≠ 3) repose sur la
PROPOSITION 8 désormais entière (injectivité du successeur, CAS 2 fermé par la
transposition construite).  On certifie chaque brique + le jalon Fini(2).
"""
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_deux import (card_un_egale_un,
                                                  card_deux_egale_deux,
                                                  deux_distinct_successeur_deux,
                                                  deux_est_un_cardinal, fini_deux)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN, DEUX, successeur, est_fini, est_cardinal
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.logique.i_1_termes_relations.formule import egal, non


def test_card_un_egale_un():
    th = card_un_egale_un()
    assert th.est_clos and th.conclusion == egal(cardinal(UN), UN)


def test_card_deux_egale_deux():
    th = card_deux_egale_deux()
    assert th.est_clos and th.conclusion == egal(cardinal(DEUX), DEUX)


def test_deux_distinct_successeur_deux():
    th = deux_distinct_successeur_deux()
    assert th.est_clos
    assert th.conclusion == non(egal(DEUX, successeur(DEUX)))   # 2 ≠ 2+1  (= 2 ≠ 3)


def test_deux_est_un_cardinal():
    th = deux_est_un_cardinal()
    assert th.est_clos and th.conclusion == est_cardinal(DEUX)


def test_fini_deux():
    th = fini_deux()
    assert th.est_clos
    assert th.conclusion == est_fini(DEUX)              # JALON : 2 EST UN ENTIER NATUREL
