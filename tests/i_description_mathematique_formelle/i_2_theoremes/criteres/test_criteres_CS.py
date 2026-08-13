"""Tests V9 — critères de substitution CS1–CS5 (identités d'assemblages).

Vérifie que la couche substitution (substitution_b_x_a, tau_x) satisfait
exactement les critères de Bourbaki §I.1.2, sur des instances concrètes
respectant les conditions de bord.

python -m pytest V9/test_criteres_CS.py -v
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import Assemblage, egalite, disjonction, negation
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations import i_1_2_criteres_CS as CS

# termes/relations concrets (lettres minuscules = termes ; = signe spécifique)
def L(n):
    return Assemblage((n,))


A_xa = egalite(L("x"), L("a"))     # (x = a)
A_xy = egalite(L("x"), L("y"))     # (x = y)
B_b = L("b")
C_c = L("c")


def test_cs1_renommage():
    # x' = z absent de A = (x=a)
    assert CS.cs1(A_xa, B_b, "x", "z") is True


def test_cs2_commutation():
    # A=(x=y), B=b, C=c ; x≠y, y∉B
    assert CS.cs2(A_xy, B_b, C_c, "x", "y") is True


def test_cs3_alpha_tau():
    assert CS.cs3(A_xa, "x", "z") is True


def test_cs4_subst_commute_tau():
    # A=(x=y), B=b ; x∉B, x≠y
    assert CS.cs4(A_xy, B_b, "x", "y") is True


def test_cs5_homomorphisme():
    assert CS.cs5_negation(A_xa, C_c, "x") is True
    assert CS.cs5_disjonction(A_xa, egalite(L("x"), L("b")), C_c, "x") is True
    assert CS.cs5_implication(A_xa, egalite(L("x"), L("b")), C_c, "x") is True
    # signe spécifique = sur des termes contenant x
    assert CS.cs5_signe(L("x"), L("a"), C_c, "x") is True


def test_cs_conditions_de_bord():
    import pytest
    with pytest.raises(ValueError):
        CS.cs1(A_xa, B_b, "x", "x")        # x' = x figure dans A
    with pytest.raises(ValueError):
        CS.cs4(A_xy, L("x"), "x", "y")     # x figure dans B


def test_cs6_conjonction():
    """CS6 (E I.29 L.14-16) : (C|x)(A et B) = (C|x)A et (C|x)B."""
    B2 = egalite(L("x"), L("b"))
    assert CS.cs6(A_xa, B2, C_c, "x") is True
    assert CS.cs6(A_xa, A_xy, C_c, "x") is True


def test_cs7_equivalence():
    """CS7 (E I.30 L.38-40) : (C|x)(A ⇔ B) = (C|x)A ⇔ (C|x)B."""
    B2 = egalite(L("x"), L("b"))
    assert CS.cs7(A_xa, B2, C_c, "x") is True
    assert CS.cs7(A_xa, A_xy, C_c, "x") is True
