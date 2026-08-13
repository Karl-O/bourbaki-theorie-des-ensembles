"""Tests §II.4 — f⁻¹⟨B∪Y⟩ = f⁻¹⟨B⟩ ∪ f⁻¹⟨Y⟩ (binaire, inconditionnel)."""
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_reciproque_reunion_binaire_ii4 import (
    image_reciproque_reunion_binaire, cible_image_reciproque_reunion_binaire)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E


def test_clos_0_hyp():
    thm = image_reciproque_reunion_binaire()
    assert thm.est_clos is True
    assert thm.hypotheses == frozenset()


def test_conclusion_egale_cible_bourbaki():
    thm = image_reciproque_reunion_binaire()
    assert thm.conclusion == cible_image_reciproque_reunion_binaire()


def test_theorie_inchangee_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22
