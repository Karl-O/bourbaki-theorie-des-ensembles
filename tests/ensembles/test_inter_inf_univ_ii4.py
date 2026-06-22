"""Test §II.4 — propriété universelle (inf) de l'intersection d'une famille."""
from bourbaki.ensembles.familles.ensembles_inter_inf_univ_ii4 import (
    inter_inf_universelle, cible_inter_inf_universelle)
from bourbaki.ensembles import ensembles_abrege as E


def test_inter_inf_universelle_close():
    thm = inter_inf_universelle()
    assert thm.est_clos
    assert thm.hypotheses == frozenset()
    assert thm.conclusion == cible_inter_inf_universelle()
    assert len(E.theorie_ensembles().axiomes) == 22
