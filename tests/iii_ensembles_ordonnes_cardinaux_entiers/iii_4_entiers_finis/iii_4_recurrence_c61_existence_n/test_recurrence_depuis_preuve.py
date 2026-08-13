# -*- coding: utf-8 -*-
"""Tests §III.4.3 — variante 2 « récurrence à partir de k » (E III.33), DÉRIVÉE de C61."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    hypothese_recurrence_depuis, conclusion_recurrence_depuis)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_depuis_preuve import (
    s_depuis, s_depuis_en_zero, heredite_s_depuis, recurrence_depuis)


def R(t):
    """R renvoyant une FORMULE (Leibniz s6 sur R{·})."""
    return appartient(t, var("Wd"))


def test_s_depuis_zero():
    """{R{k}, card(k)} ⊢ S{0} = (k≤0) ⇒ R{0}."""
    th = s_depuis_en_zero(R)
    assert th.conclusion == s_depuis(R, var("kdep"), ZERO)
    assert th.hypotheses == frozenset({hypothese_recurrence_depuis(R, var("kdep"), "ndep"),
                                       est_cardinal(var("kdep"))})


def test_heredite_depuis():
    th = heredite_s_depuis(R)
    assert th.hypotheses == frozenset({hypothese_recurrence_depuis(R, var("kdep"), "ndep"),
                                       est_cardinal(var("kdep"))})


def test_recurrence_depuis_variante2():
    """⊢ (∀n)((n entier et n≥k) ⇒ R{n}) sous {hyp, card k, predecesseur_fini_universel}."""
    th = recurrence_depuis(R)
    assert th.conclusion == conclusion_recurrence_depuis(R, var("kdep"), "ndep")
    assert len(th.hypotheses) == 3
    assert hypothese_recurrence_depuis(R, var("kdep"), "ndep") in th.hypotheses
    assert est_cardinal(var("kdep")) in th.hypotheses
