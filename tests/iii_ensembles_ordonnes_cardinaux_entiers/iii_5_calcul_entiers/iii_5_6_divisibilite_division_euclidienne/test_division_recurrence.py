# -*- coding: utf-8 -*-
"""Test §III.5.6 — briques d'assemblage de la division (récurrence forte, suite).

_diff_inf_egal : (a−b) ≤ a au niveau ENSEMBLE (sans est_cardinal(a−b), anti-circularité).
_diff_est_fini : Fini(a−b) via fini_downward_thm (résidus C61 : principe_recurrence + cardinal_pas_entre)."""
import pytest
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_recurrence import (
    _diff_inf_egal, enonce_diff_inf_egal, _diff_est_fini, enonce_diff_est_fini,
    _diff_strict, enonce_diff_strict)

pytestmark = pytest.mark.slow


def test_diff_inf_egal():
    """⊢ {card a, card b, b≤a} (a−b) ≤ a  (niveau ensemble, sans est_cardinal(a−b))."""
    r = _diff_inf_egal()
    assert r.conclusion == enonce_diff_inf_egal()
    assert len(r.hypotheses) == 3


def test_diff_est_fini():
    """⊢ {card a, card b, b≤a, Fini a, + résidus C61} Fini(a−b)."""
    r = _diff_est_fini()
    assert r.conclusion == enonce_diff_est_fini()
    assert len(r.hypotheses) == 6


def test_diff_strict():
    """⊢ {card a, card b, b≤a, Fini a, Fini b, b≠0} (a−b) < a  (route SANS commutativité, SANS résidu C61)."""
    r = _diff_strict()
    assert r.conclusion == enonce_diff_strict()
    assert len(r.hypotheses) == 6


def test_theorie_inchangee():
    _diff_inf_egal()
    assert len(E.theorie_ensembles().axiomes) == 22
