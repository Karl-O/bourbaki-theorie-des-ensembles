# -*- coding: utf-8 -*-
"""Tests §III.2.4 — Corollaire 1 du Théorème 2 (Zorn), E III.21 : maximal m ≥ a."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    est_inductif)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn_corollaires import (
    enonce_cor1, zorn_cor1_maximal_superieur)


def test_cor1_conclusion_et_hypotheses():
    """⊢ { est_inductif(G,E), a∈E } ⊢ (∃m)(element_maximal(G,E,m) et (a,m)∈G)."""
    G, E_set, a = var("Gzc"), var("Ezc"), var("azc")
    th = zorn_cor1_maximal_superieur()
    assert th.conclusion == enonce_cor1()
    # exactement les deux hypothèses honnêtes du corollaire (Zorn est CLOS)
    assert th.hypotheses == frozenset({est_inductif(G, E_set), appartient(a, E_set)})


def test_cor1_theorie_inchangee():
    """L'axiome dédié de F ne modifie pas theorie_ensembles (= 22)."""
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import (
        theorie_ensembles)
    zorn_cor1_maximal_superieur()
    assert len(theorie_ensembles().axiomes) == 22
