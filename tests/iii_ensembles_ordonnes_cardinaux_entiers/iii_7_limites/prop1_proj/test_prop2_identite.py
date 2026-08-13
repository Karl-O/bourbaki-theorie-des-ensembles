# -*- coding: utf-8 -*-
"""Tests — Prop. 2 §III.7.2, 2ᵉ assertion : moitié gauche.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites import (
    ensembles_limites as L,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_fibres import (
    famille_fibres,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop2_identite import (
    point_dans_produit_fibres, point_dans_limite_fibres,
    point_dans_limite_depuis_u, REPORTES,
)


def test_point_dans_produit_fibres():
    """🎯 z ∈ ∏ M_α — 2 hypothèses.

    Trois des quatre clauses se lisent sur « z ∈ lim←_I ».  ⚠️ z n'est PAS un
    objet construit : elles ne sont donc pas closes, elles sont DÉDUITES — même
    résultat, raison différente."""
    th = point_dans_produit_fibres()
    assert th.conclusion == appartient(
        var("zf"), E.produit_famille(famille_fibres(), var("I")))
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_point_dans_limite_fibres_reutilise_la_condition_1():
    """👑 z ∈ lim← M_α — 2 hypothèses.

    LE POINT : la condition (1) ne dépend que de f, ≤ et I, jamais de la
    famille.  Celle du système des fibres est LITTÉRALEMENT la même formule que
    celle du système de départ : on la lit une fois sur « z ∈ lim←_I » et on la
    réutilise, au lieu de la redémontrer.  C'est ce qui rend l'assemblage court."""
    th = point_dans_limite_fibres()
    assert th.conclusion == appartient(
        var("zf"), L.lim_proj(famille_fibres(), var("f")))
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_point_dans_limite_depuis_u():
    """👑👑 LA MOITIÉ GAUCHE de l'identité, branchée sur le côté u — 3 hyps.

    De « u(z) a les coordonnées de x' » à « z ∈ lim← M_α ».  Les deux briques se
    branchent parce que le membre gauche de `fibres_partout` EST la clause
    qu'attend `point_dans_limite_fibres` — vérifié, pas supposé."""
    th = point_dans_limite_depuis_u()
    assert th.conclusion == appartient(
        var("zf"), L.lim_proj(famille_fibres(), var("f")))
    assert len(th.hypotheses) == 3
    assert appartient(var("zf"), L.lim_proj(var("E"), var("f"))) in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_report_moitie_droite():
    """La moitié droite (extensionnalité sur E') est explicitement reportée."""
    assert len(REPORTES) == 1
    assert "EXTENSIONNALITÉ" in REPORTES[0]
