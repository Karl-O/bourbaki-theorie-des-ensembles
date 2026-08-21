# -*- coding: utf-8 -*-
"""Test brique (iii) de Cantor — g_decompose : G ∈ 2^X décomposé en quatre."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def test_g_decompose():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, inclus, egal, appartient)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_extensionnalite import (
        g_decompose)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
        deux)
    vg, vx = var("Gext"), var("Xext")
    incl, fonct, dom_eq, graphe = g_decompose()
    hyp = appartient(vg, E.exposant(vx, deux()))
    assert incl.conclusion == inclus(vg, E.produit(vx, deux()))
    assert fonct.conclusion == E.est_fonctionnel(vg)
    assert dom_eq.conclusion == egal(E.dom(vg), vx)
    assert graphe.conclusion == E.est_un_graphe(vg)
    for th in (incl, fonct, dom_eq, graphe):
        assert set(th.hypotheses) == {hyp}
    assert len(E.theorie_ensembles().axiomes) == 22


def test_valeurs_coincident():
    """Le cœur de (iii) : {G∈2^X, z∈X} ⊢ χ_{Pre(G)}(z) = G(z)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, appartient)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_extensionnalite import (
        valeurs_coincident)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
        preimage_un, deux)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_powerset import (
        chi)
    vg, vx, vz = var("Gext"), var("Xext"), var("zext")
    r = valeurs_coincident()
    Pre = preimage_un(vg, vx)
    assert r.conclusion == egal(E.valeur(chi(Pre, vx), vz), E.valeur(vg, vz))
    assert appartient(vg, E.exposant(vx, deux())) in r.hypotheses
    assert appartient(vz, vx) in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_chi_rho_identite():
    """🎯 La brique (iii) : {G∈2^X} ⊢ χ_{Pre(G)} = G."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal, appartient)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_extensionnalite import (
        chi_rho_identite)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
        preimage_un, deux)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_powerset import (
        chi)
    vg, vx = var("Gext"), var("Xext")
    r = chi_rho_identite()
    assert r.conclusion == egal(chi(preimage_un(vg, vx), vx), vg)
    assert set(r.hypotheses) == {appartient(vg, E.exposant(vx, deux()))}
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
