# -*- coding: utf-8 -*-
"""Tests §I.2.3 — (T|x)𝒯, C2 (rejoué sur une démonstration concrète), C3."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, implication, substitution_b_x_a as sub)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.i_2_3_substitutions import (
    theorie_substituee, c2_sur_demonstration, constantes, c3_sans_constante)

A, B, T = Assemblage(("A",)), Assemblage(("B",)), Assemblage(("T", "T'"))


def test_theorie_substituee():
    axiomes = (A, implication(A, B))
    assert theorie_substituee(axiomes, "A", T) == (T, implication(T, B))


def test_c2_sur_demonstration_concrete():
    """A, A⇒B, B : démonstration de 𝒯 = {A, A⇒B} ; son image (T|A) est une
    démonstration de (T|A)𝒯 — l'argument exact du livre (E I.23 L.25-33)."""
    axiomes = (A, implication(A, B))
    demo = (A, implication(A, B), B)                    # détachement final
    assert c2_sur_demonstration(demo, axiomes, "A", T)
    # et aussi en substituant dans la lettre B (qui traverse le détachement)
    assert c2_sur_demonstration(demo, axiomes, "B", T)


def test_c2_exige_une_demonstration():
    with pytest.raises(ValueError):
        c2_sur_demonstration((B,), (A,), "A", T)


def test_constantes():
    assert constantes((A, implication(A, B))) == frozenset({"A", "B"})


def test_c3_sans_constante():
    axiomes = (A, implication(A, B))
    assert c3_sans_constante(axiomes, "x", T)           # x hors constantes : 𝒯 inchangée
    with pytest.raises(ValueError):
        c3_sans_constante(axiomes, "A", T)              # A EST une constante


def test_c3_coherent_avec_substitution():
    # x ∉ constantes ⟹ (T|x)A = A pour chaque axiome (le cœur de la preuve).
    axiomes = (A, implication(A, B))
    assert all(sub(T, "x", a) == a for a in axiomes)
