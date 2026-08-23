# -*- coding: utf-8 -*-
"""Test H2 — le témoin-majorant avec la réunion de famille (contournement)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_ordre, frame_pair,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_majore_fam import (
    temoin_fam, majore_fam,
)


def test_majore_fam():
    """🎯 {p∈C, p∈𝔉, m'∈𝔉} ⊢ (p, m') ∈ Γ𝔉(E) — l'ordre d'extension, version ⋃𝔇."""
    t = majore_fam()
    vE, vC, vp = var("E"), var("Cch"), var("pmemb")
    m = temoin_fam(vC)
    assert t.conclusion == appartient(E.couple(vp, m), frame_ordre(vE))
    assert appartient(vp, vC) in t.hypotheses
    assert appartient(m, frame_pair(vE)) in t.hypotheses
    assert len(t.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
