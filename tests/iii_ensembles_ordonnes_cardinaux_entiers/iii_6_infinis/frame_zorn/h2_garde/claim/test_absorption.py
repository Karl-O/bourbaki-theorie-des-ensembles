# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_absorption.py — l'absorption 𝔟+𝔟=𝔟 au maximal."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_absorption import (
    enonce_absorption, absorption_au_maximal,
)


@pytest.mark.slow
def test_absorption_au_maximal():
    """🎯 {S₀ infini, φ₀ bijection} ⊢ Card S₀+Card S₀ = Card S₀   (~200 s)."""
    vS, vphi = var("S0"), var("phi0")
    t = absorption_au_maximal()
    assert t.conclusion == enonce_absorption("S0")
    #  les DEUX hypothèses sont des données du maximal — rien d'honnête en plus
    assert set(t.hypotheses) == {
        est_infini_ensemble(vS),
        est_bijection_de(vphi, E.produit(vS, vS), vS)}
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_enonce_absorption_est_la_conclusion():
    """L'énoncé bon marché doit coïncider avec la conclusion dérivée."""
    b = cardinal(var("S0"))
    from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
        somme_cardinale_binaire,
    )
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal
    assert enonce_absorption("S0") == egal(somme_cardinale_binaire(b, b), b)
