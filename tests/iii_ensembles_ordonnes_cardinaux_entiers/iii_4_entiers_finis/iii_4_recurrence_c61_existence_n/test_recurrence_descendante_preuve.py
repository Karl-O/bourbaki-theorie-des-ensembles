# -*- coding: utf-8 -*-
"""Tests §III.4.3 — variante 4 « récurrence descendante » (E III.33-34), via la variante 3."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, non, impl, pourtout, appartient)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    hypothese_recurrence_descendante, conclusion_recurrence_descendante)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_descendante_preuve import (
    pas_ascendant_non_R, recurrence_descendante)


def R(t):
    return appartient(t, var("Wde"))


def test_pas_ascendant_non_R():
    """{hyp descendante} ⊢ (∀m)((Fini m et a≤m et m<b et ¬R{m}) ⇒ ¬R{m+1})."""
    th = pas_ascendant_non_R(R)
    a, b, m = var("ades"), var("bdes"), var("mdes")
    attendu = pourtout("mdes", impl(
        et(et(et(est_fini(m), inf_egal_card(a, m)), inf_strict_card(m, b)), non(R(m))),
        non(R(successeur(m)))))
    assert th.conclusion == attendu
    assert th.hypotheses == frozenset({hypothese_recurrence_descendante(R, a, b, "ndes")})


def test_recurrence_descendante_variante4():
    """⊢ (∀n)((n entier et a≤n≤b) ⇒ R{n}), descendante — mêmes résidus honnêtes."""
    th = recurrence_descendante(R)
    assert th.conclusion == conclusion_recurrence_descendante(R, var("ades"), var("bdes"), "nfin")
    assert hypothese_recurrence_descendante(R, var("ades"), var("bdes"), "ndes") in th.hypotheses
    assert est_fini(var("bdes")) in th.hypotheses
