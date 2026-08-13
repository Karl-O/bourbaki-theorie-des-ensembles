"""Tests V9 — critères formatifs CF1–CF8 (sur la couche lecture)."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import Assemblage, egalite
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations import i_1_4_criteres_CF as CF

R = egalite(Assemblage(("x",)), Assemblage(("a",)))   # (x = a), relation
Sr = egalite(Assemblage(("x",)), Assemblage(("b",)))  # (x = b), relation
T_x = Assemblage(("x",))                               # terme (lettre)
T_a = Assemblage(("a",))                               # terme
T_b = Assemblage(("b",))                               # terme


def test_cf1_disjonction():
    assert CF.cf1(R, Sr) is True


def test_cf2_negation():
    assert CF.cf2(R) is True


def test_cf3_tau_terme():
    assert CF.cf3(R, "x") is True


def test_cf4_signe_relationnel():
    assert CF.cf4(T_x, T_a) is True


def test_cf5_implication():
    assert CF.cf5(R, Sr) is True


def test_cf6_renommage_frais():
    assert CF.cf6(R, "x", "z") is True


def test_cf7_renommage_preserve_espece():
    assert CF.cf7(R, "x", "y") is True          # relation reste relation
    assert CF.cf7(T_x, "x", "y") is True         # terme reste terme


def test_cf8_substitution_terme_preserve_espece():
    assert CF.cf8(R, "x", T_b) is True


def test_cf9_cf10_conjonction_equivalence():
    assert CF.cf9(R, Sr) is True
    assert CF.cf10(R, Sr) is True


def test_cf11_quantificateurs():
    assert CF.cf11(R, "x") is True               # (∃x)R, (∀x)R relations


def test_cf12_quantificateurs_typiques():
    assert CF.cf12(R, Sr, "x") is True


def test_cf13_inclusion():
    assert CF.cf13(T_a, T_b) is True             # (T ⊂ U) relation


def test_cf_conditions_de_bord():
    import pytest
    with pytest.raises(ValueError):
        CF.cf6(R, "x", "x")          # y = x figure dans R
    with pytest.raises(ValueError):
        CF.cf8(R, "x", R)            # T = R n'est pas un terme
