"""Tests V9 — congruence sous quantificateur (C31) + C29, vérifiés par le noyau.

C'est le verrou de C29–C42 : monotonie/congruence de ∃ et ∀. La route ∃ directe
(via C30 général + témoin τx(R) + S5) évite la circularité de C29.

python -m pytest V9/test_congruence_quantif.py -v
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import (Assemblage, negation, implication, equivalence, egalite,
                        existe, pour_tout)
from bourbaki.logique.propositions import SIG_PROP
from bourbaki.logique.tactiques.tactiques import a_implique_a
from bourbaki.logique.criteres import criteres_C as K
from bourbaki.logique import congruence_quantif as Q

S = SIG_PROP
X, Y = Assemblage(("x",)), Assemblage(("y",))
R = egalite(X, Y)                 # (x = y), contient x


def test_monotonie_existe():
    t = Q.monotonie_existe(a_implique_a(R, S), "x", S)
    assert t.conclusion == implication(existe("x", R), existe("x", R)) and t.est_clos


def test_monotonie_pour_tout():
    t = Q.monotonie_pour_tout(a_implique_a(R, S), "x", S)
    assert t.conclusion == implication(pour_tout("x", R), pour_tout("x", R)) and t.est_clos


def test_congruence_existe():
    t = Q.congruence_existe(K.c24_double_negation(R, S), "x", S)
    nn = negation(negation(R))
    assert t.conclusion == equivalence(existe("x", nn), existe("x", R)) and t.est_clos


def test_congruence_pour_tout():
    t = Q.congruence_pour_tout(K.c24_double_negation(R, S), "x", S)
    nn = negation(negation(R))
    assert t.conclusion == equivalence(pour_tout("x", nn), pour_tout("x", R)) and t.est_clos


def test_c29():
    t = Q.c29(R, "x", S)
    assert t.conclusion == equivalence(negation(existe("x", R)),
                                       pour_tout("x", negation(R)))
    assert t.est_clos


def test_c31_les_quatre_regles():
    # C31 = monotonie ∀/∃ (de ⊢R⇒S) + congruence ∀/∃ (de ⊢R⇔S) : les 4 marchent.
    imp = a_implique_a(R, S)
    eq = K.c24_double_negation(R, S)
    assert Q.monotonie_pour_tout(imp, "x", S).est_clos
    assert Q.monotonie_existe(imp, "x", S).est_clos
    assert Q.congruence_pour_tout(eq, "x", S).est_clos
    assert Q.congruence_existe(eq, "x", S).est_clos
