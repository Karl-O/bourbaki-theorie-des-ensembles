# -*- coding: utf-8 -*-
"""Tests §III.6 (prérequis Lemme 2) — pont a^(m+d) = a^m·a^d (brique W3a)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_valuation_iii6 import (
    exposant_somme_pont, exposant_somme_pont_cible,
)


def test_exposant_somme_pont_deux():
    """⊢ 2^(m+d) = 2^m·2^d, inconditionnel (l'instance de la 2-valuation)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        DEUX)
    r = exposant_somme_pont(DEUX)
    assert not r.hypotheses
    assert r.conclusion == exposant_somme_pont_cible(DEUX, "mvw", "dvw")
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
