"""Tests §III.5 — parité / division par deux (ensembles_parite_iii5)."""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_parite_iii5 as M


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_deux_succ_eq_clos():
    t = M.deux_succ_eq("kdse")
    assert t.est_clos and len(t.hypotheses) == 0


def test_division_par_deux_clos():
    t = M.division_par_deux()
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.division_par_deux_cible()


def test_impair_decompose_clos():
    t = M.impair_decompose()
    assert len(t.hypotheses) == 0
    assert t.conclusion == M.impair_decompose_cible()


def test_un_impair_clos():
    t = M.un_impair()
    assert t.est_clos and len(t.hypotheses) == 0


def test_deux_k_plus_un_impair_clos():
    t = M.deux_k_plus_un_impair()
    assert len(t.hypotheses) == 0


def test_pair_neq_impair_clos():
    t = M.pair_neq_impair()
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.pair_neq_impair_cible()


def test_impair_fois_impair_clos():
    t = M.impair_fois_impair()
    assert t.est_clos and len(t.hypotheses) == 0
    assert t.conclusion == M.impair_fois_impair_cible()
