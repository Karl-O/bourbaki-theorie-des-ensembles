"""Tests — §III.5 Prop 4 SURJECTIVITÉ de la translation x↦a+x : [0,b]→[a,a+b]."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop4_surj_iii5 import (
    existe_complement_somme_cardinal, existe_complement_somme_cardinal_enonce,
    additive_order_cancel, additive_order_cancel_enonce,
    prop4_surjective, prop4_surjective_enonce,
    prop4_ordre_iso, prop4_ordre_iso_enonce,
)


def test_existe_complement_somme_cardinal_close():
    t = existe_complement_somme_cardinal()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == existe_complement_somme_cardinal_enonce()


def test_additive_order_cancel_close():
    t = additive_order_cancel()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == additive_order_cancel_enonce()


def test_prop4_surjective_close():
    t = prop4_surjective()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == prop4_surjective_enonce()


def test_prop4_ordre_iso_close():
    t = prop4_ordre_iso()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == prop4_ordre_iso_enonce()


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
