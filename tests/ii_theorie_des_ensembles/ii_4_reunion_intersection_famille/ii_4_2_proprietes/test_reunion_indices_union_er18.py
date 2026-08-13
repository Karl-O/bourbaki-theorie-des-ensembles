# -*- coding: utf-8 -*-
"""Test Résumé E.R.18 item 3 (36) — ⋃_{J₁∪J₂}X_ι = (⋃_{J₁})∪(⋃_{J₂})."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_2_proprietes.ensembles_reunion_indices_union_er18 import (
    reunion_indices_union, enonce_reunion_indices_union)


def test_reunion_indices_union():
    """⊢ ⋃_{J₁∪J₂}X_ι = (⋃_{J₁}X_ι)∪(⋃_{J₂}X_ι) — CLOS, 0 hyp."""
    r = reunion_indices_union()
    assert r.conclusion == enonce_reunion_indices_union()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_theorie_inchangee():
    reunion_indices_union()
    assert len(E.theorie_ensembles().axiomes) == 22
