"""Tests — Cor. 4 §III.4, volet surj ⇒ inj (assemblage structurel)."""
import pytest

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_cor4_inj_surj_bij.ensembles_cor4_surj_inj_fin import (
    cor4_surj_implique_inj,
    cor4_surj_implique_inj_enonce,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles


def test_cor4_surj_implique_inj_clos():
    r = cor4_surj_implique_inj()
    assert r.est_clos
    assert not r.hypotheses
    assert r.conclusion == cor4_surj_implique_inj_enonce()


def test_theorie_22():
    assert len(theorie_ensembles().axiomes) == 22
