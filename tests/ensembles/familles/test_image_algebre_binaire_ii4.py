"""Tests §II.4 — algèbre binaire image directe / réciproque (E.II.25–27)."""
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.familles.ensembles_image_algebre_binaire_ii4 import (
    image_reunion_binaire, cible_image_reunion_binaire,
    image_reciproque_inter_binaire, cible_image_reciproque_inter_binaire,
    image_reciproque_difference, cible_image_reciproque_difference,
    image_inter_inclusion, cible_image_inter_inclusion,
)


def _check(thm, cible):
    assert thm.est_clos is True
    assert list(thm.hypotheses) == []
    assert thm.conclusion == cible
    assert len(E.theorie_ensembles().axiomes) == 22


def test_image_reunion_binaire():
    _check(image_reunion_binaire(), cible_image_reunion_binaire())


def test_image_reciproque_inter_binaire():
    # est_fonctionnel(f) ⇒ f⁻¹⟨B∩Y⟩ = f⁻¹⟨B⟩ ∩ f⁻¹⟨Y⟩
    _check(image_reciproque_inter_binaire(), cible_image_reciproque_inter_binaire())


def test_image_reciproque_difference():
    # est_fonctionnel(f) ⇒ f⁻¹⟨B∖Y⟩ = f⁻¹⟨B⟩ ∖ f⁻¹⟨Y⟩
    _check(image_reciproque_difference(), cible_image_reciproque_difference())


def test_image_inter_inclusion():
    # f⟨B∩Y⟩ ⊂ f⟨B⟩ ∩ f⟨Y⟩  (inclusion inconditionnelle ; égalité exigerait f injective)
    _check(image_inter_inclusion(), cible_image_inter_inclusion())
