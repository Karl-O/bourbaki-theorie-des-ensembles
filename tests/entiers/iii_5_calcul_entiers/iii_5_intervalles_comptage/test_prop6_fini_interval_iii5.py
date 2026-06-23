"""Tests §III.5 Prop 6 socle — partie « plus petit élément » (bien ordonné)."""
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop6_fini_interval_iii5 import (
    prop3_total_min, prop3_total_min_enonce,
    cor1_total_min, cor1_total_min_enonce,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def test_prop3_total_min_close():
    t = prop3_total_min()
    assert t.est_clos
    assert t.conclusion == prop3_total_min_enonce("Gppt", "Eppt")


def test_cor1_total_min_close():
    c = cor1_total_min()
    assert c.est_clos
    assert c.conclusion == cor1_total_min_enonce("Gppt", "Eppt")


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
