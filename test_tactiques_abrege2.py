"""Tests V9 — boîte à outils abrégée + ⊂-transitivité (chapitre II)."""
from __future__ import annotations

from formule import (var, egal, non, impl, equiv, et, inclus, afficher_f)
import noyau_abrege as N
import tactiques_abrege2 as T2

A = egal(var("a"), var("b"))
B = egal(var("b"), var("c"))


def test_double_negation():
    assert T2.dni(A).conclusion == impl(A, non(non(A)))
    assert T2.dne(A).conclusion == impl(non(non(A)), A)


def test_contraposition():
    c = T2.contraposition(N.assume(impl(A, B)))
    assert c.conclusion == impl(non(B), non(A))


def test_conjonction_intro_elim():
    conj = T2.conjonction_intro(N.assume(A), N.assume(B))
    assert conj.conclusion == et(A, B)
    assert T2.conjonction_elim_gauche(N.assume(et(A, B))).conclusion == A
    assert T2.conjonction_elim_droite(N.assume(et(A, B))).conclusion == B


def test_instanciation_en_x():
    R = egal(var("x"), var("a"))
    from formule import pourtout
    t = T2.instanciation_en_x(R, "x")
    assert t.conclusion == impl(pourtout("x", R), R) and t.est_clos


def test_inclusion_transitive():
    # ⊢ ((a ⊂ b) et (b ⊂ c)) ⇒ (a ⊂ c)   (théorème du chapitre II)
    t = T2.inclusion_transitive("a", "b", "c")
    cible = impl(et(inclus(var("a"), var("b")), inclus(var("b"), var("c"))),
                 inclus(var("a"), var("c")))
    assert t.conclusion == cible and t.est_clos
