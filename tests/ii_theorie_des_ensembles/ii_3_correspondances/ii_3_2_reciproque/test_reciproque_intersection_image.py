"""Test Résumé §2.7 formule (17) : f⁻¹⟨Y⟩ = f⁻¹⟨Y ∩ img f⟩."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_reciproque_intersection_image import (
    reciproque_intersection_image, cible_reciproque_intersection_image)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reciproque_intersection_image_close():
    th = reciproque_intersection_image()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible_reciproque_intersection_image()


def test_parametrable():
    th = reciproque_intersection_image("g", "Z")
    assert th.est_clos
    assert th.conclusion == cible_reciproque_intersection_image("g", "Z")
    assert len(E.theorie_ensembles().axiomes) == 22
