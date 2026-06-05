"""Tests V9 — noyau abrégé (règles sur Formule) + axiomes du chapitre II.

python -m pytest V9/test_noyau_abrege.py -v
"""
from __future__ import annotations
import pytest

from bourbaki.logique.formule import (var, egal, appartient, ou, impl, equiv, pourtout, existe,
                     tau, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

A = egal(var("a"), var("b"))
B = egal(var("b"), var("c"))
Cc = egal(var("c"), var("d"))


# ── primitives ────────────────────────────────────────────────────────────────
def test_a_implique_a():
    th = N.loi_deduction(A, N.assume(A))          # ⊢ A ⇒ A
    assert th.conclusion == impl(A, A) and th.est_clos


def test_modus_ponens():
    th = N.modus_ponens(N.assume(A), N.assume(impl(A, B)))  # {A, A⇒B} ⊢ B
    assert th.conclusion == B
    assert th.hypotheses == {A, impl(A, B)}


def test_modus_ponens_refuse_incoherent():
    with pytest.raises(ValueError):
        N.modus_ponens(N.assume(B), N.assume(impl(A, B)))   # mineure ≠ antécédent


def test_syllogisme():
    # ⊢ A⇒B, ⊢ B⇒C (supposés) ⟹ ⊢ A⇒C  (assume + MP + déduction)
    ab, bc = N.assume(impl(A, B)), N.assume(impl(B, Cc))
    h = N.assume(A)
    hc = N.modus_ponens(N.modus_ponens(h, ab), bc)          # {A,A⇒B,B⇒C} ⊢ C
    th = N.loi_deduction(A, hc)
    assert th.conclusion == impl(A, Cc)
    assert th.hypotheses == {impl(A, B), impl(B, Cc)}


def test_generalisation():
    R = egal(var("x"), var("y"))
    g = N.generalisation("x", N.loi_deduction(R, N.assume(R)))  # ⊢ (∀x)(R⇒R)
    assert g.conclusion == pourtout("x", impl(R, R)) and g.est_clos


def test_generalisation_refuse_variable_libre():
    R = egal(var("x"), var("a"))
    with pytest.raises(ValueError):
        N.generalisation("x", N.assume(R))         # x libre dans l'hypothèse R


def test_s5():
    R = egal(var("x"), var("a"))
    th = N.s5(R, var("b"), "x")                    # ⊢ (b|x)R ⇒ (∃x)R
    assert th.conclusion == impl(subst_f(var("b"), "x", R), existe("x", R))
    assert th.est_clos


def test_s6_s7():
    R = egal(var("x"), var("c"))
    t6 = N.s6(var("a"), var("b"), "x", R)
    assert t6.conclusion == impl(egal(var("a"), var("b")),
                                 equiv(subst_f(var("a"), "x", R),
                                       subst_f(var("b"), "x", R)))
    S = egal(var("x"), var("d"))
    t7 = N.s7(R, S, "x")
    assert t7.conclusion == impl(pourtout("x", equiv(R, S)),
                                 egal(tau("x", R), tau("x", S)))


# ── chapitre II : axiomes disponibles ─────────────────────────────────────────
def test_axiomes_chap2_disponibles():
    T = E.theorie_ensembles()
    a1 = N.axiome(T, E.A1)
    a2 = N.axiome(T, E.A2)
    assert a1.conclusion == E.A1 and a1.est_clos
    assert a2.conclusion == E.A2 and a2.est_clos


def test_theoreme_inforgeable():
    with pytest.raises(PermissionError):
        N.Theoreme(frozenset(), A, "faux", object())


def test_alpha_tau_renomme_liant():
    """⊢ τx(R) = τy((y|x)R) — α-renommage d'un τ-terme (reflet CS1), théorème CLOS.

    Exemple : valeur(F,t,"c") = valeur(F,t,"y") (τc((t,c)∈F) = τy((t,y)∈F))."""
    vt, vF = var("t"), var("F")
    R = appartient(E.couple(vt, var("c")), vF)        # (t,c)∈F
    thm = N.alpha_tau(R, "c", "y")
    assert thm.conclusion == egal(E.valeur(vF, vt, "c"), E.valeur(vF, vt, "y"))
    assert thm.est_clos


def test_alpha_tau_refuse_capture():
    """Garde-fou : alpha_tau REFUSE un renommage capturant (y libre dans R) —
    il ne peut donc jamais fabriquer une fausse égalité de τ-termes."""
    vt, vF = var("t"), var("F")
    R = appartient(E.couple(vt, var("c")), vF)        # « t » libre dans R
    with pytest.raises(ValueError):
        N.alpha_tau(R, "c", "t")                       # renommer c→t capturerait t
