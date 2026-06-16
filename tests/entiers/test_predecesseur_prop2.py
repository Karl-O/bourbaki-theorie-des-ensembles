"""Tests — §III.5 PROPOSITION 2 : « tout entier ≠ 0 est un successeur ».

Ferme le résidu `predecesseur_fini_universel` (Prop. 2) sous l'UNIQUE résidu
`recollement_bijection_universel` (bijectivité du recollement canonique de deux
ensembles disjoints, Prop. 10 §II.4) ; puis N_existe = ℕ existe sous ce seul résidu."""
import pytest

from bourbaki.logique.formule import var, egal, et, impl, non, existe, pourtout, appartient
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.entiers.ensembles_entiers import est_fini, successeur, ZERO

from bourbaki.entiers.ensembles_principe_recurrence_preuve import (
    predecesseur_fini, predecesseur_fini_universel,
)
from bourbaki.entiers.ensembles_N_collectivise import _coll_fini

import bourbaki.entiers.ensembles_predecesseur_prop2 as P


# ────────────────────────────────────────────────────────────────────────────
#  INVARIANT : theorie inchangée = 22
# ────────────────────────────────────────────────────────────────────────────
def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ────────────────────────────────────────────────────────────────────────────
#  helpers de surgery
# ────────────────────────────────────────────────────────────────────────────
def test_disjoint_diff_singleton_clos():
    d = P._disjoint_diff_singleton("Xt", "x0t")
    assert d.est_clos and len(d.hypotheses) == 0
    assert d.conclusion == egal(
        E.intersection(E.difference(var("Xt"), E.singleton(var("x0t"))),
                       E.singleton(var("x0t"))), E.VIDE)


def test_singleton_inclus_clos():
    s = P.singleton_inclus("x0t", "Et")
    assert s.est_clos and len(s.hypotheses) == 0


def test_eq_retire_ajoute_residu_unique():
    """eq_retire_ajoute a pour UNIQUE hypothèse recollement_bijection_universel."""
    era = P.eq_retire_ajoute("Xt", "x0t")
    assert not era.est_clos
    assert len(era.hypotheses) == 1
    assert P.recollement_bijection_universel() in era.hypotheses


def test_m_egal_successeur_card_diff_residu_unique():
    me = P.m_egal_successeur_card_diff("mt", "x0t")
    assert len(me.hypotheses) == 1
    assert P.recollement_bijection_universel() in me.hypotheses


def test_k_inf_strict_m_clos():
    """k < m (depuis Fini m, est_cardinal(k), m=successeur(k)) est INCONDITIONNEL."""
    ks = P._k_inf_strict_m("mks", "kks")
    assert ks.est_clos and len(ks.hypotheses) == 0


# ────────────────────────────────────────────────────────────────────────────
#  🎯 PROPOSITION 2 — predecesseur_fini_universel
# ────────────────────────────────────────────────────────────────────────────
def test_predecesseur_fini_universel_conclusion_exacte():
    """conclusion ÉGALE LITTÉRALEMENT predecesseur_fini_universel(k='kpred') — la VRAIE
    Prop. 2 (vraie pour TOUT m fini > 0), PAS une tautologie."""
    pf = P.predecesseur_fini_universel_preuve()
    assert pf.conclusion == predecesseur_fini_universel(k="kpred")
    # NON vacuité : la conclusion n'est aucune des hypothèses
    assert pf.conclusion not in pf.hypotheses


def test_predecesseur_fini_universel_residu_unique():
    """UNIQUE résidu honnête = recollement_bijection_universel (theorie=22, rien postulé)."""
    pf = P.predecesseur_fini_universel_preuve()
    assert len(pf.hypotheses) == 1
    assert P.recollement_bijection_universel() in pf.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


# ────────────────────────────────────────────────────────────────────────────
#  🎯🎯 ℕ EXISTE (sous le SEUL résidu recollement_bijection_universel)
# ────────────────────────────────────────────────────────────────────────────
def test_N_existe_conclusion_coll_fini():
    n = P.N_existe()
    assert n.conclusion == _coll_fini("x")
    assert n.conclusion not in n.hypotheses


def test_N_existe_residu_unique():
    """coll(x, Fini x) sous le SEUL recollement_bijection_universel : predecesseur_fini_
    universel est DÉCHARGÉ ; ℕ existe modulo ce seul résidu (Prop. 10 §II.4)."""
    n = P.N_existe()
    assert len(n.hypotheses) == 1
    assert P.recollement_bijection_universel() in n.hypotheses
    assert predecesseur_fini_universel(k="kpred") not in n.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
