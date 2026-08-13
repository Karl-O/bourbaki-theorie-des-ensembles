# -*- coding: utf-8 -*-
"""Tests — conditions (i)-(iv) et énoncés du Th. 1 §III.7.4 (page E III.59)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Formule,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_7_limites.th1_proj.ensembles_th1_conditions import (
    stable_par_intersections, propriete_intersection_finie,
    filtrant_decroissant_non_vide, condition_iii, condition_iv,
    cible_th1_a, cible_th1_b, REPORTES,
)


def test_conditions_sont_des_formules():
    """Les 5 conditions et les 2 cibles sont des formules bien construites."""
    for f in (stable_par_intersections("S", "I"),
              propriete_intersection_finie("S", "I"),
              filtrant_decroissant_non_vide("S", "I"),
              condition_iii("E", "f", "S", "I"),
              condition_iv("f", "S", "I"),
              cible_th1_a("E", "f", "I"),
              cible_th1_b("E", "f", "I")):
        assert isinstance(f, Formule)


def test_reports_honnetes():
    """Les preuves du Th. 1 sont explicitement reportées (pas de faux acquis)."""
    assert len(REPORTES) == 2
    assert len(E.theorie_ensembles().axiomes) == 22
