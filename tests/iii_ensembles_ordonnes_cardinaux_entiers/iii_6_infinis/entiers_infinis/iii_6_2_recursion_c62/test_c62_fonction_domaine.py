# -*- coding: utf-8 -*-
"""Test §III.6.2 — C62 fonction globale, fichier 2 : dom(f) = E.

(⊆) CLOS ; (⊇) et l'égalité sous les 3 résidus C62 {bo, essais_bien_formes,
rule_codomain}.  Règle OPAQUE T(t)=app('Trule',t).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import app, var, egal
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
    fonction_globale,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_domaine import (
    dom_fonction_inclus_e, e_inclus_dom_fonction, dom_fonction_globale,
)

_T = lambda t: app("Trule", t)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_dom_inclus_e_clos():
    """(⊆) ⊢ dom(⋃𝔇_tot) ⊂ E — CLOS, 0 hyp."""
    th = dom_fonction_inclus_e(_T)
    assert th.est_clos


def test_e_inclus_dom():
    """(⊇) {bo, ebf, rc} ⊢ E ⊂ dom(⋃𝔇_tot) — 3 hyps = résidus C62."""
    th = e_inclus_dom_fonction(_T)
    assert len(th.hypotheses) == 3


def test_dom_egal_e():
    """🎯 {bo, ebf, rc} ⊢ dom(f) = E."""
    th = dom_fonction_globale(_T)
    assert th.conclusion == egal(E.dom(fonction_globale()), var("Enat"))
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
