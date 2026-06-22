"""Test §II.4 — propriété universelle (sup) de la réunion d'une famille."""
from bourbaki.ensembles.familles.ensembles_reunion_sup_univ_ii4 import (
    reunion_sup_universelle, cible_reunion_sup_universelle)
from bourbaki.ensembles import ensembles_abrege as E


def test_reunion_sup_universelle_close():
    thm = reunion_sup_universelle()
    assert thm.est_clos
    assert thm.hypotheses == frozenset()
    assert thm.conclusion == cible_reunion_sup_universelle()
    assert len(E.theorie_ensembles().axiomes) == 22
