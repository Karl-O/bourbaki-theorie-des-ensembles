# -*- coding: utf-8 -*-
"""Test §III.6.2 — C62 pont restriction, fichier 5 : f|seg(x) = p|seg(x).

Règle OPAQUE T(t)=app('Trule',t).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import app
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_restriction import (
    essai_inclus_fonction, restriction_essai_incluse,
    restriction_fonction_incluse, restriction_egale_essai_seg,
)

_T = lambda t: app("Trule", t)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_essai_inclus_fonction():
    """{p∈𝔇_tot} ⊢ p ⊂ ⋃𝔇_tot."""
    th = essai_inclus_fonction(_T)
    assert len(th.hypotheses) == 1


def test_restriction_essai_incluse():
    """{p∈𝔇_tot} ⊢ p|A ⊂ f|A (sens facile)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    th = restriction_essai_incluse(_T, var("Aseg"))
    assert len(th.hypotheses) == 1


def test_restriction_fonction_incluse():
    """{p∈𝔇_tot, est_essai(p,x)} ⊢ f|seg(x) ⊂ p|seg(x) (le sens dur)."""
    th = restriction_fonction_incluse(_T)
    assert len(th.hypotheses) == 2


def test_restriction_egale_essai_seg():
    """🎯 {p∈𝔇_tot, est_essai(p,x)} ⊢ f|seg(x) = p|seg(x)."""
    th = restriction_egale_essai_seg(_T)
    assert th.conclusion.tag == "="
    assert len(th.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22
