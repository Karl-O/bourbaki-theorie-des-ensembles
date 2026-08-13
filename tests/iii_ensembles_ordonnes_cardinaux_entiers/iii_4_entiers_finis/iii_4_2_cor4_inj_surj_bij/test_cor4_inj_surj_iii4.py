"""Tests — Cor. 4 §III.4, direction inj ⇒ surj (cor4_inj_implique_surj)."""
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_cor4_inj_surj_bij.ensembles_cor4_inj_surj_iii4 import (
    cor4_inj_implique_surj, cor4_inj_implique_surj_enonce,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles


def test_cor4_inj_implique_surj_close():
    t = cor4_inj_implique_surj()
    assert t.est_clos
    assert not t.hypotheses
    assert t.conclusion == cor4_inj_implique_surj_enonce()


def test_theorie_intacte():
    assert len(theorie_ensembles().axiomes) == 22
