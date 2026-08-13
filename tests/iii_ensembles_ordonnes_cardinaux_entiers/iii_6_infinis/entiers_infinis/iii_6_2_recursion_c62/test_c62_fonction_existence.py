# -*- coding: utf-8 -*-
"""Test §III.6.2 — C62 fonction globale, fichier 3 : (∃f)(func ∧ dom=E ∧ équation).

Règle OPAQUE T(t)=app('Trule',t).  3 hyps = résidus C62.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import app
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_existence import (
    valeur_fonction_globale, equation_fonction_globale,
    c62_fonction_cible, fonction_recursion_c62,
)

_T = lambda t: app("Trule", t)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_valeur_au_point():
    """{z∈E, bo, ebf, rc} ⊢ valeur(f,z)=T(z) — 4 hyps."""
    th = valeur_fonction_globale(_T)
    assert len(th.hypotheses) == 4


def test_equation_universelle():
    """{bo, ebf, rc} ⊢ (∀z∈E)(valeur(f,z)=T(z)) — 3 hyps."""
    th = equation_fonction_globale(_T)
    assert len(th.hypotheses) == 3


def test_fonction_recursion_c62():
    """🎯🎯 {bo, ebf, rc} ⊢ (∃f)(func ∧ dom=E ∧ équation) — LA conclusion C62."""
    th = fonction_recursion_c62(_T)
    assert th.conclusion == c62_fonction_cible(_T)
    assert th.conclusion.tag == "exists"
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
