# -*- coding: utf-8 -*-
"""Test brique (iv) de Cantor — la bijection Y ↦ ((χ_Y, A), 2), sous-lemme (a)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E


def test_bijection_fonctionnel_et_domaine():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
        var, egal)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_bijection import (
        bijection_graphe, bijection_fonctionnel, bijection_domaine)
    vA = var("Abij")
    B = bijection_graphe()
    f = bijection_fonctionnel()
    d = bijection_domaine()
    assert not f.hypotheses and not d.hypotheses
    assert d.conclusion == egal(E.dom(B), E.parties(vA))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_bijection_injective():
    """(b) : B injectif sur P(A), clos."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_bijection import (
        bijection_graphe, bijection_injective)
    vA = var("Abij")
    r = bijection_injective()
    assert not r.hypotheses
    assert r.conclusion == E.injective_dans(bijection_graphe(), E.parties(vA))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_bijection_image():
    """(c) : image(B, P(A)) = 𝓕(A;2), clos."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_bijection import (
        bijection_graphe, bijection_image)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
        deux)
    vA = var("Abij")
    r = bijection_image()
    assert not r.hypotheses
    assert r.conclusion == E.est_surjective(
        bijection_graphe(), E.parties(vA), E.applications(vA, deux()))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_bijection_equipotent():
    """🎯 (d) : Eq(P(A), 𝓕(A;2)), clos — la brique (iv) entière."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_prop12_bijection import (
        bijection_equipotent)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        equipotent)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.prop12_powerset.ensembles_powerset_deux import (
        deux)
    vA = var("Abij")
    r = bijection_equipotent()
    assert not r.hypotheses
    assert r.conclusion == equipotent(E.parties(vA), E.applications(vA, deux()))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
