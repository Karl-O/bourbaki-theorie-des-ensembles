"""Tests Prop 4 §III.5 — stricte croissance et injectivité de la translation entière."""
from bourbaki.entiers.ensembles_prop4_strict_iii5 import (
    prop4_translation_injective, prop4_translation_injective_enonce,
    prop4_translation_stricte, prop4_translation_stricte_enonce,
)
from bourbaki.ensembles import ensembles_abrege as E


def test_injective_close():
    res = prop4_translation_injective()
    assert res.est_clos
    assert not res.hypotheses
    assert res.conclusion == prop4_translation_injective_enonce()


def test_stricte_close():
    res = prop4_translation_stricte()
    assert res.est_clos
    assert not res.hypotheses
    assert res.conclusion == prop4_translation_stricte_enonce()


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
