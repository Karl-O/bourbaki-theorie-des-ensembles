# -*- coding: utf-8 -*-
"""Tests §I.4.1 — (∃x), (∀x) via τ ; CS8, CS9, C26 (E I.32)."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, negation, substitution_b_x_a, tau_x, lettres)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_1_quantificateurs import (
    existe, pour_tout, cs8, cs9, c26_identite)

R = Assemblage(("=", "x", "y"))          # la relation x = y


def test_existe_est_l_abreviation():
    assert existe("x", R) == substitution_b_x_a(tau_x(R, "x"), "x", R)
    assert "x" not in lettres(existe("x", R))     # x n'est plus libre


def test_pour_tout_est_l_abreviation():
    assert pour_tout("x", R) == negation(existe("x", negation(R)))


def test_facade_compatible():
    from bourbaki.i_description_mathematique_formelle.assemblage import existe as x2, pour_tout as t2
    assert x2 is existe and t2 is pour_tout


def test_cs8_renommage_du_lie():
    """CS8 (E I.32 L.7-11) : x'∉R ⟹ (∃x)R = (∃x')R', R' = (x'|x)R."""
    assert cs8(R, "x", "z")
    with pytest.raises(ValueError):
        cs8(R, "x", "y")                              # y figure dans R


def test_cs9_commutation_substitution():
    """CS9 (E I.32 L.12-18) : x∉U, x≠y ⟹ (U|y)(∃x)R = (∃x)(U|y)R."""
    U = Assemblage(("u", "v"))
    assert cs9(R, U, "x", "y")
    with pytest.raises(ValueError):
        cs9(R, Assemblage(("x",)), "x", "y")          # x figure dans U
    with pytest.raises(ValueError):
        cs9(R, U, "x", "x")                           # x = y


def test_c26_identite():
    """C26 (E I.32 L.33-36) : (∀x)R est identique à non non (τ_x(non R)|x)R."""
    assert c26_identite(R, "x")
    assert c26_identite(R, "z")                       # x hors de R : dégénéré mais vrai
