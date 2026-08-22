# -*- coding: utf-8 -*-
"""Tests K6d briques 1-2 — l'itérée évite x0, la simplification par u."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_injectivite_iteree import (
    x0_hors_image, g_succ_evite_x0, succ_simplification,
)

_U, _X0, _E = var("uld"), var("xze"), var("Eld")


def test_g_succ_evite_x0():
    """{5 hyps} ⊢ (∀n∈ℕ)(¬(g(succ n)=x0))."""
    t = g_succ_evite_x0(_U, _X0, _E)
    assert len(t.hypotheses) == 5
    assert x0_hors_image(_U, _X0, _E) in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_succ_simplification():
    """{5 hyps} ⊢ (∀m)(∀n)((m,n∈ℕ ∧ g(succ m)=g(succ n)) ⇒ g(m)=g(n))."""
    t = succ_simplification(_U, _X0, _E)
    assert len(t.hypotheses) == 5
    assert E.injective_dans(_U, _E) in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
