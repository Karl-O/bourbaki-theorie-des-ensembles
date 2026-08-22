# -*- coding: utf-8 -*-
"""Tests §III.6 (prérequis Lemme 2) — 2-valuation : unicité par récurrence C61."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, impl
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, DEUX,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_valuation_recurrence import (
    exposant_zero_un, ops_produit_un_droite, deux_valuation_unique, _P, _card_deux,
)


def test_exposant_zero_un():
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
        exposant_cardinal_binaire)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        ZERO, UN)
    r = exposant_zero_un(DEUX)
    assert not r.hypotheses
    assert r.conclusion == egal(exposant_cardinal_binaire(DEUX, ZERO), UN)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_deux_valuation_unique():
    """🎯 W3 : ⊢ Fini m ⇒ (∀mp∀u∀up)((finitudes ∧ impairs ∧ 2^m·u=2^mp·up) ⇒ m=mp ∧ u=up)."""
    vm = var("mdv")
    r = deux_valuation_unique()
    assert not r.hypotheses
    assert r.conclusion == impl(est_fini(vm), _P(vm))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
