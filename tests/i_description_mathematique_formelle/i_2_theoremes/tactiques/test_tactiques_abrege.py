"""Tests V9 — tactiques abrégées + 1er théorème du chapitre II (réflexivité de ⊂)."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, impl, inclus, afficher_f
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a, syllogisme, inclusion_reflexive

A = egal(var("a"), var("b"))
B = egal(var("b"), var("c"))
Cc = egal(var("c"), var("d"))


def test_a_implique_a():
    assert a_implique_a(A).conclusion == impl(A, A)


def test_syllogisme():
    ab, bc = N.assume(impl(A, B)), N.assume(impl(B, Cc))
    t = syllogisme(ab, bc)
    assert t.conclusion == impl(A, Cc)
    assert t.hypotheses == {impl(A, B), impl(B, Cc)}


def test_inclusion_reflexive():
    # ⊢ x ⊂ x  (premier théorème du chapitre II)
    t = inclusion_reflexive("x")
    assert t.conclusion == inclus(var("x"), var("x"))
    assert t.est_clos


def test_inclusion_reflexive_affichage():
    t = inclusion_reflexive("x")
    # s'affiche comme (∀z)(z∈x ⇒ z∈x)
    assert afficher_f(t.conclusion) == "(∀z) ((z ∈ x) ⇒ (z ∈ x))"
