"""Tests — §III.4-5 pigeonhole forme équipotente (partie_equipotente_egale)."""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_partie_equipotente_finie import (
    partie_equipotente_egale, partie_equipotente_egale_enonce,
)


def test_partie_equipotente_egale_close():
    r = partie_equipotente_egale()
    assert r.est_clos
    assert not r.hypotheses
    assert r.conclusion == partie_equipotente_egale_enonce()


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
