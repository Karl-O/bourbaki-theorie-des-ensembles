"""Tests des critères typiques C39, C40, C42 (Bourbaki E I.37).

Chaque test APPELLE le théorème et compare la conclusion à la CIBLE par égalité
structurelle (==), vérifie les hypothèses exactes et le caractère clos. Les atomes
A, R, S, B sont des relations sans la lettre liée (x, y) — la fraîcheur exigée par
C39/C42 est donc satisfaite, et l'hypothèse de C39 reste exactement {A⇒(R⇒S)}.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, non, et, ou, impl, equiv,
                     existe, appartient)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_4_criteres_typiques_c39_c42 import (
    existe_typique, pourtout_typique,
    c39_existe_typique, c39_pourtout_typique,
    c40_existe_typique, c40_pourtout_typique,
    c42_existe_typique, c42_pourtout_typique)


# ── atomes (relations sans x ni y) ────────────────────────────────────────────
A = appartient(var("a"), var("EA"))
B = appartient(var("b"), var("EB"))
R = appartient(var("r"), var("ER"))
S = appartient(var("s"), var("ES"))
X, Y = "x", "y"


# ── C39 — monotonie typique (hypothèse A⇒(R⇒S)) ──────────────────────────────
def test_c39_existe_typique():
    t = c39_existe_typique(A, R, S, X)
    cible = impl(existe_typique(A, X, R), existe_typique(A, X, S))
    assert t.conclusion == cible
    assert t.hypotheses == frozenset({impl(A, impl(R, S))})
    assert not t.est_clos
    assert cible not in t.hypotheses


def test_c39_pourtout_typique():
    t = c39_pourtout_typique(A, R, S, X)
    cible = impl(pourtout_typique(A, X, R), pourtout_typique(A, X, S))
    assert t.conclusion == cible
    assert t.hypotheses == frozenset({impl(A, impl(R, S))})
    assert not t.est_clos
    assert cible not in t.hypotheses


# ── C40 — distribution typique (théorèmes purs) ──────────────────────────────
def test_c40_existe_typique():
    t = c40_existe_typique(A, R, S, X)
    cible = equiv(existe_typique(A, X, ou(R, S)),
                  ou(existe_typique(A, X, R), existe_typique(A, X, S)))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_c40_pourtout_typique():
    t = c40_pourtout_typique(A, R, S, X)
    cible = equiv(pourtout_typique(A, X, et(R, S)),
                  et(pourtout_typique(A, X, R), pourtout_typique(A, X, S)))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


# ── C42 — commutation typique (x∉B, y∉A) ─────────────────────────────────────
def test_c42_existe_typique():
    t = c42_existe_typique(A, B, R, X, Y)
    cible = equiv(existe_typique(A, X, existe_typique(B, Y, R)),
                  existe_typique(B, Y, existe_typique(A, X, R)))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_c42_pourtout_typique():
    t = c42_pourtout_typique(A, B, R, X, Y)
    cible = equiv(pourtout_typique(A, X, pourtout_typique(B, Y, R)),
                  pourtout_typique(B, Y, pourtout_typique(A, X, R)))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


# ── garde-fou des conditions de fraîcheur C42 ────────────────────────────────
def test_c42_refuse_fraicheur_violee():
    import pytest
    # x figure dans B  → refus
    Bx = appartient(var("x"), var("EB"))
    with pytest.raises(ValueError):
        c42_existe_typique(A, Bx, R, X, Y)
    # y figure dans A  → refus
    Ay = appartient(var("y"), var("EA"))
    with pytest.raises(ValueError):
        c42_pourtout_typique(Ay, B, R, X, Y)
