"""Tests — §III.6.3 frame_a_maximal_clos : exposé des 2 résidus honnêtes de Zorn."""
import pytest

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import libres_f
from bourbaki.cardinaux.ensembles_frame_maximal_clos import (
    residu_H1, residu_H2, residus_honnetes,
    frame_a_maximal_clos, hessenberg_a_carre_egal_a_0hyp,
)


def test_residus_enonces():
    """Les 2 résidus sont des formules E-niveau bien formées."""
    rs = residus_honnetes("E")
    assert len(rs) == 2
    for h in rs:
        assert set(libres_f(h)) <= {"E"}


def test_frame_a_maximal_clos():
    """frame_a_maximal_clos : (∃m)maximal sous EXACTEMENT {H1, H2}, theorie=22."""
    before = len(E.theorie_ensembles().axiomes)
    res = frame_a_maximal_clos("E")
    assert set(res.hypotheses) == {residu_H1("E"), residu_H2("E")}
    assert res.conclusion not in res.hypotheses
    for h in res.hypotheses:
        assert set(libres_f(h)) <= {"E"}
    assert len(E.theorie_ensembles().axiomes) == 22 == before


@pytest.mark.slow
def test_hessenberg_a_carre_egal_a_0hyp():
    """a²=a (enonce_hessenberg) sous EXACTEMENT les 2 résidus de Zorn.  LENT (~10min)."""
    from bourbaki.cardinaux.ensembles_hessenberg import enonce_hessenberg
    res = hessenberg_a_carre_egal_a_0hyp("E")
    assert res.conclusion == enonce_hessenberg("E")
    assert set(res.hypotheses) == {residu_H1("E"), residu_H2("E")}
    assert res.conclusion not in res.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
