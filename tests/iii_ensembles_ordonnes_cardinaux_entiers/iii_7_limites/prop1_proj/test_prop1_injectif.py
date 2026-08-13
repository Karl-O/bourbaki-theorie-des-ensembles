# -*- coding: utf-8 -*-
"""Tests — Prop. 1 2° §III.7.2 : critère d'injectivité projectif.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.prop1_proj.ensembles_prop1_injectif import (
    coordonnees_egales_points, images_graphes_points,
)


def test_coordonnees_egales_points():
    """🎯 Deux points de F de mêmes coordonnées ont même image — 5 hyps.

    Six auparavant : la prémisse « images-graphes » n'est plus supposée mais
    déduite de u(y), u(z) ∈ lim← (`point_limite_est_graphe`, §7.1)."""
    th = coordonnees_egales_points()
    assert len(th.hypotheses) == 5
    assert images_graphes_points(var("u"), var("F"), "yy", "zz") not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
