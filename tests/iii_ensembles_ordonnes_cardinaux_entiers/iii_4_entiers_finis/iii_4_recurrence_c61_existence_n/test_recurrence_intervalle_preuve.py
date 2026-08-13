# -*- coding: utf-8 -*-
"""Tests §III.4.3 — variante 3 « récurrence limitée à [a,b] » (E III.33), DÉRIVÉE de C61."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    hypothese_recurrence_intervalle, conclusion_recurrence_intervalle)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_intervalle_preuve import (
    s_intervalle, s_intervalle_en_zero, heredite_s_intervalle, recurrence_intervalle)


def R(t):
    return appartient(t, var("Wi"))


def _hyp():
    return hypothese_recurrence_intervalle(R, var("aint"), var("bint"), "nint")


def test_s_intervalle_zero():
    th = s_intervalle_en_zero(R)
    assert th.conclusion == s_intervalle(R, var("aint"), var("bint"), ZERO)
    assert th.hypotheses == frozenset({_hyp(), est_cardinal(var("aint"))})


def test_heredite_intervalle():
    th = heredite_s_intervalle(R)
    assert th.hypotheses == frozenset({_hyp(), est_cardinal(var("aint"))})


def test_recurrence_intervalle_variante3():
    """⊢ (∀n)((n entier et a≤n≤b) ⇒ R{n}) sous {hyp, card a, predecesseur_fini_universel}."""
    th = recurrence_intervalle(R)
    assert th.conclusion == conclusion_recurrence_intervalle(R, var("aint"), var("bint"), "nint")
    assert len(th.hypotheses) == 3
    assert _hyp() in th.hypotheses
    assert est_cardinal(var("aint")) in th.hypotheses
