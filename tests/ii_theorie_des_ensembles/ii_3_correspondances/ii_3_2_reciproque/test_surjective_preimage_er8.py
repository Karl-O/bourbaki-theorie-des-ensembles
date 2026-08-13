# -*- coding: utf-8 -*-
"""Test Résumé E.R.8 item 7 — surjectivité ⇔ image réciproque non vide."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_surjective_preimage_er8 import (
    surjective_ssi_preimage_non_vide, enonce_surjective_ssi_preimage)


def test_surjective_ssi_preimage_non_vide():
    """⊢ est_application(f,E,F) ⇒ (surj ⇔ (∀X)(X⊂F ⇒ (X≠∅ ⇒ f⁻¹⟨X⟩≠∅))) — CLOS."""
    r = surjective_ssi_preimage_non_vide()
    assert r.conclusion == enonce_surjective_ssi_preimage()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_theorie_inchangee():
    """La dérivation n'ajoute aucun axiome : theorie_ensembles reste à 22."""
    surjective_ssi_preimage_non_vide()
    assert len(E.theorie_ensembles().axiomes) == 22
