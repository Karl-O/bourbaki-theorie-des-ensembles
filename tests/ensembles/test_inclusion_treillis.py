"""Tests §II.1 — caractérisations de ⊂ par ∩/∪ (A⊂B ⇔ A∩B=A ; A⊂B ⇔ A∪B=B).

Honnêteté LCF : CLOS (0 hyp), conclusion == l'ÉQUIVALENCE fidèle (inclus ⇔ égalité),
les deux membres DIFFÈRENT, theorie = 22.
"""
from bourbaki.logique.formule import var, equiv, inclus, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_inclusion_treillis as M

A, B = var("A"), var("B")


def test_inclusion_ssi_intersection_egale():
    t = M.inclusion_ssi_intersection_egale()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == equiv(inclus(A, B), egal(E.intersection(A, B), A))
    assert inclus(A, B) != egal(E.intersection(A, B), A)


def test_inclusion_ssi_reunion_egale():
    t = M.inclusion_ssi_reunion_egale()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == equiv(inclus(A, B), egal(E.reunion(A, B), B))
    assert inclus(A, B) != egal(E.reunion(A, B), B)


def test_theorie_inchangee_22():
    M.inclusion_ssi_intersection_egale()
    M.inclusion_ssi_reunion_egale()
    assert len(E.theorie_ensembles().axiomes) == 22
