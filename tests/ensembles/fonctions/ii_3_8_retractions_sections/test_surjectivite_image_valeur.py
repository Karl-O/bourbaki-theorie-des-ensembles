"""Test §II.3 — pont surjectivité image↔valeur : y∈f⟨A⟩ ⇒ (∃x∈A) y=f(x).

APPEL du théorème, conclusion == cible reconstruite, clôture (0 hyp), theorie==22.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_8_retractions_sections.ensembles_surjectivite_image_valeur import (
    surjective_image_donne_valeur, cible_surjective_image_donne_valeur)


def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_surjective_image_donne_valeur():
    """⊢ est_fonctionnel(f) ⇒ (∀y)(y∈f⟨A⟩ ⇒ (∃x)(x∈A et y=f(x)))."""
    th = surjective_image_donne_valeur()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible_surjective_image_donne_valeur()
    assert len(E.theorie_ensembles().axiomes) == 22
