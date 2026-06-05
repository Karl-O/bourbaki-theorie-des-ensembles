"""Tests V9 — C34, C35, C38 (sous-ensemble verrouillé de C32–C42)."""
from __future__ import annotations

from assemblage import (Assemblage, negation, conjonction, implication,
                        equivalence, egalite, existe, pour_tout)
from propositions import A, B, SIG_PROP
import criteres_quantif2 as Q2

S = SIG_PROP
X, Y = Assemblage(("x",)), Assemblage(("y",))
R = egalite(X, Y)


def test_c34_pour_tout():
    t = Q2.c34_pour_tout(R, "x", "y", S)
    assert t.conclusion == equivalence(pour_tout("x", pour_tout("y", R)),
                                       pour_tout("y", pour_tout("x", R)))
    assert t.est_clos


def test_c34_existe():
    t = Q2.c34_existe(R, "x", "y", S)
    assert t.conclusion == equivalence(existe("x", existe("y", R)),
                                       existe("y", existe("x", R)))
    assert t.est_clos


def test_c35_quantificateur_typique():
    t = Q2.c35(A, B, "x", S)
    cible = equivalence(negation(existe("x", conjonction(A, negation(B)))),
                        pour_tout("x", implication(A, B)))
    assert t.conclusion == cible and t.est_clos


def test_c38_1_demorgan_typique():
    t = Q2.c38_1(A, B, "x", S)
    ex = existe("x", conjonction(A, negation(B)))
    assert t.conclusion == equivalence(negation(negation(ex)), ex) and t.est_clos
