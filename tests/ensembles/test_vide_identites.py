"""Tests §II.1 — identités de l'ensemble vide (∅ neutre/absorbant, A∖∅, A∖A).

Honnêteté LCF : chaque théorème est CLOS (0 hyp), conclusion == l'ÉGALITÉ FIDÈLE
littérale, membres distincts, theorie = 22.
"""
from bourbaki.logique.formule import var, egal
from bourbaki.ensembles import ensembles_abrege as E
import bourbaki.ensembles.ensembles_vide_identites as M

A, V = var("A"), E.VIDE
U, I, D = E.reunion, E.intersection, E.difference


def _check(t, lhs, rhs):
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == egal(lhs, rhs)
    assert lhs != rhs


def test_reunion_vide_neutre():
    _check(M.reunion_vide_neutre(), U(A, V), A)


def test_intersection_vide():
    _check(M.intersection_vide(), I(A, V), V)


def test_difference_vide_neutre():
    _check(M.difference_vide_neutre(), D(A, V), A)


def test_difference_self():
    _check(M.difference_self(), D(A, A), V)


def test_theorie_inchangee_22():
    for f in M.__all__:
        getattr(M, f)()
    assert len(E.theorie_ensembles().axiomes) == 22
