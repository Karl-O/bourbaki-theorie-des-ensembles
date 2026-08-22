# -*- coding: utf-8 -*-
"""Test §III.4.2 Prop. 2 (gardée) : cardinal ≤ entier ⇒ entier."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_prop2_fini_downward import (
    prop2_fini_downward, prop2_fini_downward_cible,
)


def test_prop2_fini_downward():
    """🎯 ⊢ est_cardinal(a) ⇒ (∀x)((a≤x ∧ Fini x) ⇒ Fini a), clos."""
    r = prop2_fini_downward()
    assert not r.hypotheses
    assert r.conclusion == prop2_fini_downward_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
