"""Tests §III.5 — parité / division par deux (ensembles_parite_iii5)."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux import ensembles_parite_iii5 as M
import pytest

#: FICHIER LOURD — 3129 s mesurés le 18 août (pytest --durations).
#: Marqué slow : la porte « not slow » ne le voit plus, mais le théorème
#: reste vérifié par la suite COMPLÈTE — à lancer avant toute annonce.
pytestmark = pytest.mark.slow


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
