# -*- coding: utf-8 -*-
"""Tests §I.2 — démonstrations comme suites d'assemblages (E I.21-25)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, implication)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.i_2_2_demonstration import (
    est_demonstration, est_theoreme, premiere_faute)

A = Assemblage(("=", "a", "b"))
B = Assemblage(("=", "b", "c"))
AXIOMES = (A, implication(A, B))


def test_demonstration_valide():
    # A (axiome), A⇒B (axiome), B (déduit de A et A⇒B)
    suite = (A, implication(A, B), B)
    assert est_demonstration(suite, AXIOMES)
    assert premiere_faute(suite, AXIOMES) is None
    assert est_theoreme(B, suite, AXIOMES)


def test_rejet_terme_non_justifie():
    # B affirmé AVANT que A⇒B ne figure : rien ne le justifie.
    suite = (A, B, implication(A, B))
    assert premiere_faute(suite, AXIOMES) == 1
    assert not est_demonstration(suite, AXIOMES)
    assert not est_theoreme(B, suite, AXIOMES)


def test_suite_vide_nest_pas_une_demonstration():
    assert not est_demonstration((), AXIOMES)


def test_theoreme_doit_figurer_dans_la_suite():
    suite = (A, implication(A, B), B)
    C = Assemblage(("=", "c", "d"))
    assert not est_theoreme(C, suite, AXIOMES)
