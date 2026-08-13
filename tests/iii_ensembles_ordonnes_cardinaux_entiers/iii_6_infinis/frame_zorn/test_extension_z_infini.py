# -*- coding: utf-8 -*-
"""Tests — dérivations RÉUNION du cadre Hessenberg (Z infini, Card F_r).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, libres_f
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_extension_z_infini import (
    z_infini_derive, cadre_card_trois_b_reunion,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini_ensemble


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_z_infini_derive():
    """🎯 est_infini_ensemble(S₀∪U) — l'ex-« mur ¬(∃X) » de B2, DÉRIVÉ ; résidus Ucadre-libres."""
    th = z_infini_derive()
    Z = E.reunion(var("S0"), var("Ucadre"))
    assert th.conclusion == est_infini_ensemble(Z)
    assert est_infini_ensemble(var("S0")) in th.hypotheses
    for h in th.hypotheses:
        assert "Ucadre" not in libres_f(h)
    assert th.conclusion not in th.hypotheses


def test_cadre_card_trois_b_reunion():
    """🎯 Card(F_r) = 𝔟 — le cardinal du cadre-RÉUNION, via les ponts d'équipotence."""
    th = cadre_card_trois_b_reunion()
    vS, vU = var("S0"), var("Ucadre")
    F_r = E.reunion(E.produit(vS, vU),
                    E.reunion(E.produit(vU, vS), E.produit(vU, vU)))
    assert th.conclusion == egal(cardinal(F_r), cardinal(vS))
    assert len(th.hypotheses) == 5
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
