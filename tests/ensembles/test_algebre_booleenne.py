"""Tests §II.1 — associativité / idempotence / absorption de ∪ et ∩ (égalités).

Honnêteté LCF : chaque théorème est CLOS (0 hyp), sa conclusion est l'ÉGALITÉ FIDÈLE
littérale annoncée, les deux membres DIFFÈRENT (non trivial), theorie = 22.
"""
from bourbaki.logique.formule import var, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_algebre_booleenne as M

A, B, C, Ev = var("A"), var("B"), var("C"), var("E")
U, I, D = E.reunion, E.intersection, E.difference


def _check(t, lhs, rhs):
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == egal(lhs, rhs)
    assert lhs != rhs                                  # égalité NON triviale


def test_associativite_reunion():
    _check(M.associativite_reunion(), U(U(A, B), C), U(A, U(B, C)))


def test_associativite_intersection():
    _check(M.associativite_intersection(), I(I(A, B), C), I(A, I(B, C)))


def test_idempotence_reunion():
    _check(M.idempotence_reunion(), U(A, A), A)


def test_idempotence_intersection():
    _check(M.idempotence_intersection(), I(A, A), A)


def test_absorption_reunion():
    _check(M.absorption_reunion(), U(A, I(A, B)), A)


def test_absorption_intersection():
    _check(M.absorption_intersection(), I(A, U(A, B)), A)


def test_distributivite_intersection_reunion():
    _check(M.distributivite_intersection_reunion(), I(A, U(B, C)), U(I(A, B), I(A, C)))


def test_distributivite_reunion_intersection():
    _check(M.distributivite_reunion_intersection(), U(A, I(B, C)), I(U(A, B), U(A, C)))


def test_de_morgan_complement_reunion():
    _check(M.de_morgan_complement_reunion(), D(Ev, U(A, B)), I(D(Ev, A), D(Ev, B)))


def test_de_morgan_complement_intersection():
    _check(M.de_morgan_complement_intersection(), D(Ev, I(A, B)), U(D(Ev, A), D(Ev, B)))


def test_theorie_inchangee_22():
    for f in M.__all__:
        getattr(M, f)()
    assert len(E.theorie_ensembles().axiomes) == 22
