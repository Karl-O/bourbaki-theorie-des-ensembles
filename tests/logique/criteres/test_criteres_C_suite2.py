"""Tests V9 — équivalences C24/C25 longues, re-vérifiées par le noyau."""
from __future__ import annotations

from bourbaki.assemblage.assemblage import (negation, disjonction, conjonction, implication, equivalence)
from bourbaki.logique.i_1_termes_relations.propositions import A, B, C, SIG_PROP
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from bourbaki.logique.i_2_criteres_C.criteres import criteres_C_suite2 as KS2

S = SIG_PROP


def test_c24_assoc_et():
    t = KS2.c24_assoc_et(A, B, C, S)
    assert t.conclusion == equivalence(conjonction(A, conjonction(B, C)),
                                       conjonction(conjonction(A, B), C))
    assert t.est_clos


def test_c24_demorgan():
    t = KS2.c24_demorgan(A, B, S)
    assert t.conclusion == equivalence(disjonction(A, B),
                                       negation(conjonction(negation(A), negation(B))))
    assert t.est_clos


def test_c24_et_non():
    t = KS2.c24_et_non(A, B, S)
    assert t.conclusion == equivalence(conjonction(A, negation(B)),
                                       negation(implication(A, B)))
    assert t.est_clos


def test_c25_second():
    t = KS2.c25_second(noyau.assume(negation(A), S), B, S)   # sous l'hypothèse ¬A
    assert t.conclusion == equivalence(disjonction(A, B), B)
    assert t.hypotheses == {negation(A)}
