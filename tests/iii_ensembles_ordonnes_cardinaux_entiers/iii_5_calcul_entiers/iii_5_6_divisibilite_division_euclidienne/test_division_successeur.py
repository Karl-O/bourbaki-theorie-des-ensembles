# -*- coding: utf-8 -*-
"""Test §III.5.6 — identité du successeur b·(q+1M) = b + b·q (division euclidienne)."""
import pytest

from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_successeur as M

pytestmark = pytest.mark.slow


def test_division_successeur():
    """⊢ Card(b × Card(q⊔{∅})) = Card(b ⊔ Card(b×q)) — clos, cible exacte, 22 axiomes."""
    t = M.division_successeur()
    assert t.conclusion == M.division_successeur_cible()
    assert t.est_clos
    assert len(theorie_ensembles().axiomes) == 22
