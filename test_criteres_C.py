"""Tests V9 — re-vérification des critères C7–C25 (couverture Phase A).

Chaque critère est reconstruit via les tactiques V9 et le NOYAU doit confirmer
la conclusion exacte. C'est la re-vérification indépendante (« encore et encore »)
des résultats du workflow de couverture.

python -m pytest V9/test_criteres_C.py -v
"""
from __future__ import annotations

from assemblage import (negation, disjonction, implication, conjonction, equivalence)
from propositions import A, B, C, SIG_PROP
import noyau
from tactiques import a_implique_a
from tactiques_prop import tiers_exclu
import criteres_C as K

S = SIG_PROP


def test_c7():
    assert K.c7(A, B, S).conclusion == implication(B, disjonction(A, B))


def test_c10_tiers_exclu():
    assert K.c10(A, S).conclusion == disjonction(A, negation(A))


def test_c11_c16_double_negation():
    assert K.c11(A, S).conclusion == implication(A, negation(negation(A)))
    assert K.c16(A, S).conclusion == implication(negation(negation(A)), A)


def test_c12_contraposition():
    assert K.c12(A, B, S).conclusion == implication(implication(A, B),
                                                     implication(negation(B), negation(A)))


def test_c17():
    t = K.c17(A, B, S)
    assert t.conclusion == implication(implication(negation(B), negation(A)),
                                       implication(A, B))
    assert t.est_clos


def test_c21_projections():
    assert K.c21g(A, B, S).conclusion == implication(conjonction(A, B), A)
    assert K.c21d(A, B, S).conclusion == implication(conjonction(A, B), B)


def test_c24_double_negation_equiv():
    assert K.c24_double_negation(A, S).conclusion == equivalence(negation(negation(A)), A)


# ── règles ────────────────────────────────────────────────────────────────────

def test_c9_affaiblissement():
    base = noyau.s1(A, S)                              # ⊢ (A∨A)⇒A
    assert K.c9(base, B, S).conclusion == implication(B, base.conclusion)


def test_c13():
    ab = a_implique_a(A, S)                            # ⊢ A⇒A  (donc B=A)
    t = K.c13(ab, C, S)
    assert t.conclusion == implication(implication(A, C), implication(A, C))


def test_c14_deduction():
    t = K.c14(A, noyau.assume(A, S), S)                # ⊢ A⇒A (primitive C6)
    assert t.conclusion == implication(A, A) and t.est_clos


def test_c15_absurde():
    h = noyau.assume(implication(negation(A), A), S)   # {¬A⇒A} ⊢ ¬A⇒A
    t = K.c15(h, A, S)
    assert t.conclusion == A                            # déduit A (sous l'hypothèse)


def test_c18_disjonction_des_cas():
    t = K.c18(noyau.assume(disjonction(A, B), S),
              noyau.assume(implication(A, C), S),
              noyau.assume(implication(B, C), S), S)
    assert t.conclusion == C


def test_c20_conjonction():
    t = K.c20(a_implique_a(A, S), a_implique_a(B, S), S)
    assert t.conclusion == conjonction(implication(A, A), implication(B, B)) and t.est_clos


def test_c22_equivalence_sym_trans():
    eqAB = noyau.assume(equivalence(A, B), S)
    assert K.c22_symetrie(eqAB, S).conclusion == equivalence(B, A)
    eqBC = noyau.assume(equivalence(B, C), S)
    assert K.c22_transitivite(eqAB, eqBC, S).conclusion == equivalence(A, C)


def test_c23_negation():
    eqAB = noyau.assume(equivalence(A, B), S)
    assert K.c23_negation(eqAB, S).conclusion == equivalence(negation(A), negation(B))


def test_c25_premier_cas():
    t = K.c25_premier(a_implique_a(A, S), B, S)        # A := (A⇒A), théorème
    assert t.conclusion == equivalence(conjonction(implication(A, A), B), B)
    assert t.est_clos
