"""Tests — Cor 4 §III.4, volet surj ⇒ inj (cœur honnête : section finie ⇒ bijective)."""
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_cor4_inj_surj_bij.ensembles_cor4_surj_inj_iii4 import (
    section_finie_implique_bijective,
    section_finie_implique_bijective_enonce,
)
import pytest

#: FICHIER LOURD — 735 s mesurés le 18 août (pytest --durations).
#: Marqué slow : la porte « not slow » ne le voit plus, mais le théorème
#: reste vérifié par la suite COMPLÈTE — à lancer avant toute annonce.
pytestmark = pytest.mark.slow


def test_section_finie_implique_bijective_close():
    thm = section_finie_implique_bijective()
    assert thm.est_clos
    assert not thm.hypotheses
    assert thm.conclusion == section_finie_implique_bijective_enonce()


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
