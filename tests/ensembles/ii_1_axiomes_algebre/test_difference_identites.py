"""Tests §II.1 — identités de la différence (A∩(B∖C), (A∖B)∖C).

Honnêteté LCF : CLOS (0 hyp), conclusion == égalité fidèle, membres distincts, theorie = 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_difference_identites as M

A, B, C = var("A"), var("B"), var("C")
I, D, U = E.intersection, E.difference, E.reunion


def _check(t, lhs, rhs):
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == egal(lhs, rhs)
    assert lhs != rhs


def test_intersection_difference_associe():
    _check(M.intersection_difference_associe(), I(A, D(B, C)), D(I(A, B), C))


def test_difference_reunion():
    _check(M.difference_reunion(), D(D(A, B), C), D(A, U(B, C)))


def test_theorie_inchangee_22():
    for f in M.__all__:
        getattr(M, f)()
    assert len(E.theorie_ensembles().axiomes) == 22
