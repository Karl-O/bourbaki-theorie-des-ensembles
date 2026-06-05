"""Tests V9 — boîte à outils propositionnelle, généralisation, et ⊢ x = x.

python -m pytest V9/test_reflexivite.py -v
Démo lisible :  python V9/test_reflexivite.py
"""
from __future__ import annotations

from assemblage import (
    Assemblage, negation, implication, conjonction, equivalence,
    egalite, pour_tout,
)
import noyau
import tactiques as T
import tactiques_prop as P
from tactiques_egalite import instanciation_en_x, reflexivite

A = Assemblage(("=", "a", "b"))
B = Assemblage(("=", "b", "c"))


# ── Monotonie de ∨ ────────────────────────────────────────────────────────────

def test_mono_droite_gauche():
    s1 = noyau.s1(A)                               # ⊢ (A∨A)⇒A
    md = T.mono_droite(s1, B)                      # ⊢ (B∨(A∨A))⇒(B∨A)
    p, q = T.antecedent_consequent(md.conclusion)
    assert md.est_clos
    mg = T.mono_gauche(s1, B)                      # ⊢ ((A∨A)∨B)⇒(A∨B)
    assert mg.est_clos


# ── Double négation, contraposition, conjonction ──────────────────────────────

def test_double_negation():
    assert P.double_negation_intro(A).conclusion == implication(A, negation(negation(A)))
    assert P.double_negation_elim(A).conclusion == implication(negation(negation(A)), A)
    assert P.double_negation_intro(A).est_clos
    assert P.double_negation_elim(A).est_clos


def test_contraposition():
    impl = noyau.assume(implication(A, B))         # (A⇒B) ⊢ (A⇒B)
    c = P.contraposition(impl)                     # (A⇒B) ⊢ (¬B ⇒ ¬A)
    assert c.conclusion == implication(negation(B), negation(A))


def test_conjonction_intro_et_equivalence():
    a_aa = noyau.s1(A)                             # ⊢ (A∨A)⇒A
    a_a = T.a_implique_a(A)                         # ⊢ A⇒A
    conj = P.conjonction_intro(a_aa, a_a)          # ⊢ ((A∨A)⇒A) et (A⇒A)
    assert conj.conclusion == conjonction(a_aa.conclusion, a_a.conclusion)
    assert conj.est_clos
    equiv = P.equivalence_reflexive(A)             # ⊢ A ⇔ A
    assert equiv.conclusion == equivalence(A, A) and equiv.est_clos


# ── Généralisation (C27) ──────────────────────────────────────────────────────

def test_generalisation():
    aa = T.a_implique_a(A)                          # ⊢ A⇒A (clos)
    g = noyau.generalisation("x", aa)               # ⊢ (∀x)(A⇒A)
    assert g.conclusion == pour_tout("x", implication(A, A))


def test_generalisation_refuse_variable_libre_dans_hypothese():
    # x figure dans l'hypothèse → généralisation interdite.
    R = Assemblage(("=", "x", "a"))
    h = noyau.assume(R)                             # {x=a} ⊢ (x=a)
    import pytest
    with pytest.raises(ValueError):
        noyau.generalisation("x", h)


# ── Instanciation (C30) et réflexivité ────────────────────────────────────────

def test_instanciation_en_x():
    R = Assemblage(("=", "x", "a"))
    inst = instanciation_en_x(R, "x")              # ⊢ (∀x)R ⇒ R
    assert inst.conclusion == implication(pour_tout("x", R), R)
    assert inst.est_clos


def test_reflexivite_x_egal_x():
    th = reflexivite("x")                           # ⊢ x = x
    assert th.conclusion == egalite(Assemblage(("x",)), Assemblage(("x",)))
    assert th.est_clos
    assert th.hypotheses == frozenset()


if __name__ == "__main__":
    th = reflexivite("x")
    print("Théorème vérifié :", th)
    print("conclusion == (x = x) :",
          th.conclusion == egalite(Assemblage(("x",)), Assemblage(("x",))))
    print("hypothèses :", set(th.hypotheses) or "∅ (théorème clos)")
