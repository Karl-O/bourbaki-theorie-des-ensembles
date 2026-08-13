# -*- coding: utf-8 -*-
"""Tests §III.4.3 — variantes du principe de récurrence (E III.33-34)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, impl, pourtout, app)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    s_recurrence_forte, hypothese_recurrence_forte, conclusion_recurrence,
    hypothese_recurrence_depuis, conclusion_recurrence_depuis,
    hypothese_recurrence_intervalle, conclusion_recurrence_intervalle,
    hypothese_recurrence_descendante, conclusion_recurrence_descendante)


def R(t):
    return app("Rrel", t)


def test_s_forte():
    n, p = var("n"), var("pfor")
    attendu = pourtout("pfor", impl(et(et(est_fini(n), est_fini(p)),
                                       inf_strict_card(p, n)), R(p)))
    assert s_recurrence_forte(R, n) == attendu


def test_variante1_hypothese_et_conclusion():
    n = var("nfor")
    assert hypothese_recurrence_forte(R) == \
        pourtout("nfor", impl(s_recurrence_forte(R, n), R(n)))
    assert conclusion_recurrence(R) == \
        pourtout("nfor", impl(est_fini(n), R(n)))


def test_variante2_depuis_k():
    k, n = var("k"), var("ndep")
    hyp = hypothese_recurrence_depuis(R, k)
    attendu = et(R(k), pourtout("ndep",
        impl(et(et(est_fini(n), inf_egal_card(k, n)), R(n)), R(successeur(n)))))
    assert hyp == attendu
    assert conclusion_recurrence_depuis(R, k) == \
        pourtout("ndep", impl(et(est_fini(n), inf_egal_card(k, n)), R(n)))


def test_variante3_intervalle():
    a, b, n = var("a"), var("b"), var("nint")
    hyp = hypothese_recurrence_intervalle(R, a, b)
    attendu = et(R(a), pourtout("nint",
        impl(et(et(et(est_fini(n), inf_egal_card(a, n)),
                   inf_strict_card(n, b)), R(n)),
             R(successeur(n)))))
    assert hyp == attendu
    assert conclusion_recurrence_intervalle(R, a, b) == \
        pourtout("nint", impl(et(et(est_fini(n), inf_egal_card(a, n)),
                                 inf_egal_card(n, b)), R(n)))


def test_variante4_descendante():
    a, b, n = var("a"), var("b"), var("ndes")
    hyp = hypothese_recurrence_descendante(R, a, b)
    attendu = et(R(b), pourtout("ndes",
        impl(et(et(et(est_fini(n), inf_egal_card(a, n)),
                   inf_strict_card(n, b)), R(successeur(n))),
             R(n))))
    assert hyp == attendu
    # même conclusion que la variante 3 (l'induction descend au lieu de monter)
    assert conclusion_recurrence_descendante(R, a, b, "nint") == \
        conclusion_recurrence_intervalle(R, a, b, "nint")
