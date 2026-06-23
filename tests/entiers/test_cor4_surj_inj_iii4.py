"""Tests — Cor 4 §III.4, volet surj ⇒ inj (cœur honnête : section finie ⇒ bijective)."""
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_cor4_inj_surj_bij.ensembles_cor4_surj_inj_iii4 import (
    section_finie_implique_bijective,
    section_finie_implique_bijective_enonce,
)


def test_section_finie_implique_bijective_close():
    thm = section_finie_implique_bijective()
    assert thm.est_clos
    assert not thm.hypotheses
    assert thm.conclusion == section_finie_implique_bijective_enonce()


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
