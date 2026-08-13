"""Tests V9 — re-vérification des équivalences C23–C25, C28 (couverture Phase B).

Le noyau doit confirmer la conclusion exacte de chaque équivalence.

python -m pytest V9/test_criteres_C_suite.py -v
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import (negation, disjonction, conjonction, implication,
                        equivalence, existe, pour_tout)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_propositions import A, B, C, SIG_PROP
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.criteres import criteres_C_suite as KS

S = SIG_PROP


def _eqAB():
    return noyau.assume(equivalence(A, B), S)


# ── C23 (sous l'hypothèse A⇔B) ────────────────────────────────────────────────

def test_c23_impl_droite():
    t = KS.c23_impl_droite(_eqAB(), C, S)
    assert t.conclusion == equivalence(implication(A, C), implication(B, C))
    assert t.hypotheses == {equivalence(A, B)}


def test_c23_impl_gauche():
    t = KS.c23_impl_gauche(_eqAB(), C, S)
    assert t.conclusion == equivalence(implication(C, A), implication(C, B))


def test_c23_et():
    t = KS.c23_et(_eqAB(), C, S)
    assert t.conclusion == equivalence(conjonction(A, C), conjonction(B, C))


def test_c23_ou():
    t = KS.c23_ou(_eqAB(), C, S)
    assert t.conclusion == equivalence(disjonction(A, C), disjonction(B, C))


# ── C24 (closes) ──────────────────────────────────────────────────────────────

def test_c24_contraposition():
    t = KS.c24_contraposition(A, B, S)
    assert t.conclusion == equivalence(implication(A, B),
                                       implication(negation(B), negation(A)))
    assert t.est_clos


def test_c24_idempotence():
    assert KS.c24_idem_et(A, S).conclusion == equivalence(conjonction(A, A), A)
    assert KS.c24_idem_ou(A, S).conclusion == equivalence(disjonction(A, A), A)


def test_c24_commutativite():
    assert KS.c24_comm_et(A, B, S).conclusion == equivalence(conjonction(A, B), conjonction(B, A))
    assert KS.c24_comm_ou(A, B, S).conclusion == equivalence(disjonction(A, B), disjonction(B, A))


def test_c24_ou_implique():
    t = KS.c24_ou_implique(A, B, S)
    assert t.conclusion == equivalence(disjonction(A, B), implication(negation(A), B))
    assert t.est_clos


# ── C28 ───────────────────────────────────────────────────────────────────────

def test_c28_demorgan_quantificateurs():
    t = KS.c28(A, "x", S)                       # R = atome A
    cible = equivalence(negation(pour_tout("x", A)), existe("x", negation(A)))
    assert t.conclusion == cible and t.est_clos
