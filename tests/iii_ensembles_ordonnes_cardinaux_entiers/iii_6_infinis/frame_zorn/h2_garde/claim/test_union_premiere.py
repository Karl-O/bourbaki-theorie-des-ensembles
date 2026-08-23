# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_union_premiere.py — le pont membre → ⋃S(C)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_union_premiere import (
    pr1_inclus_union,
)


def test_pr1_inclus_union():
    """🎯 { u ∈ C } ⊢ pr₁(u) ⊂ ⋃S(C).

    Brique commune aux quatre dernières données du recollement — les seules
    qui mêlent la famille 𝔇 et la réunion US.  Emploie `membre_union_premiere`
    dans le sens ARRIÈRE : S5 introduit l'existentielle au témoin u."""
    vC, vu = var("Cch"), var("umem")
    t = pr1_inclus_union()
    assert t.conclusion == inclus(E.pr1(vu), union_premiere(vC), "xup")
    assert list(t.hypotheses) == [appartient(vu, vC)]
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
