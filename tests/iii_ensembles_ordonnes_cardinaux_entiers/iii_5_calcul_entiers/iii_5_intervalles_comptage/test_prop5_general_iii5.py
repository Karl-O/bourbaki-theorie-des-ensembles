"""Tests — §III.5 Prop 5 GÉNÉRALE : Card([a,b]) = (b−a)+1  (E III.38)."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_general_iii5 import (
    prop5_intervalle_general, prop5_intervalle_general_enonce,
    somme_diff_egale_grand,
)


def test_prop5_intervalle_general_close():
    t = prop5_intervalle_general()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == prop5_intervalle_general_enonce()


def test_somme_diff_egale_grand_close():
    s = somme_diff_egale_grand()
    assert s.est_clos and not s.hypotheses


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
