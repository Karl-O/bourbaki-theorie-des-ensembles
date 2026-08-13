# -*- coding: utf-8 -*-
"""Tests — la restriction au demi-intervalle, elle aussi sans arithmétique."""
from __future__ import annotations

import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from outils_ia.conjectures.goldbach import est_premier
from recherche.additif.demi_abstrait import (
    moitie_implique_rencontre, rencontre_demi, restriction_a_la_moitie,
)


def _clos(th):
    return th.est_clos and not th.hypotheses


def test_affaiblissement_immediat():
    """⊢ ∀k( rencontre dans [0,k] ⇒ rencontre dans [0,2k] ) — on oublie la borne."""
    th = moitie_implique_rencontre()
    assert _clos(th)
    assert rencontre_demi().tag == "exists"
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_restriction_sans_ouvrir_S():
    """⊢ ∀k( Fini k ⇒ ( rencontre_S(2k) ⇒ rencontre dans [0,k] ) ).

    L'assemblage symétrie + demi-intervalle ne réintroduit PAS d'arithmétique :
    `S` reste un paramètre opaque de bout en bout.

    Lent : le demi-intervalle paie la récurrence de la simplification additive."""
    th = restriction_a_la_moitie()
    assert _clos(th)
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_la_meme_preuve_sur_la_primalite():
    """La même, avec `S := est_premier` — c'est le cas Goldbach.

    Si ce test et le précédent passent tous deux, l'assemblage ne peut pas
    contenir d'information sur les nombres premiers : il ferme aussi bien
    sans."""
    th = restriction_a_la_moitie(S=lambda x: est_premier(x, d="d1", q="q1"))
    assert _clos(th)
    assert len(E.theorie_ensembles().axiomes) == 22
