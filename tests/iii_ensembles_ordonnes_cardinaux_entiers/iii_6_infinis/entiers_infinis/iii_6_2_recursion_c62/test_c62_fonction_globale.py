# -*- coding: utf-8 -*-
"""Test §III.6.2 — C62 fonction globale, fichier 1 : f=⋃𝔇_tot FONCTIONNELLE (CLOS).

Règle OPAQUE T(t)=app('Trule',t) (motif des tests C60/C62 déposés).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import app, var
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import (
    Dtot, membre_Dtot, fonction_globale, coincidence_membres_tot,
    fonction_globale_fonctionnelle,
)

_T = lambda t: app("Trule", t)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_membre_Dtot():
    """L'axiome S8 instancié : p∈𝔇_tot ⇔ (ambiant ∧ (∃n∈E) est_essai(p,n))."""
    th = membre_Dtot(_T)
    assert th.conclusion.tag == "non"          # ⇔ (encodé et/ou/non) en tête
    assert th.est_clos


def test_coincidence_membres_tot():
    """⊢ coincidence_membres(𝔇_tot) — CLOS (valeurs épinglées sur la règle)."""
    th = coincidence_membres_tot(_T)
    assert th.est_clos


def test_fonction_globale_fonctionnelle():
    """🎯 ⊢ est_fonctionnel(⋃𝔇_tot) — CLOS, 0 hyp, theorie==22."""
    th = fonction_globale_fonctionnelle(_T)
    assert th.est_clos
    assert th.conclusion == E.est_fonctionnel(fonction_globale())
    assert len(E.theorie_ensembles().axiomes) == 22
