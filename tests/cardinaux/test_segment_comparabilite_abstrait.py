"""Test §III.2 — comparabilité de deux segments abstraits (brique de Lemme 1)."""
from bourbaki.logique.formule import var, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_segment_comparabilite_abstrait as SC


def _Rf(g):
    vg = var(g)
    return lambda a, b: appartient(E.couple(a, b), vg)


def test_segments_abstraits_comparables():
    """{ bo, est_segment(S,R,E), est_segment(S',R,E) } ⊢ (S⊂S') ou (S'⊂S)."""
    t = SC.segments_abstraits_comparables()
    assert not t.est_clos
    assert len(t.hypotheses) == 3
    assert t.conclusion == SC.segments_abstraits_comparables_cible()
    assert t.conclusion not in t.hypotheses
    # les 2 segments sont bien des hypothèses
    Rf = _Rf("R")
    assert E.est_segment(var("S"), Rf, var("E")) in t.hypotheses
    assert E.est_segment(var("Sp"), Rf, var("E")) in t.hypotheses


def test_parametrable():
    t = SC.segments_abstraits_comparables("Rp", "F", "A", "B")
    assert len(t.hypotheses) == 3
    assert t.conclusion == SC.segments_abstraits_comparables_cible("Rp", "F", "A", "B")


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
