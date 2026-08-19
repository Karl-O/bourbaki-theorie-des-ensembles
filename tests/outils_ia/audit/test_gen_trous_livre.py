# -*- coding: utf-8 -*-
"""Tests — le détecteur de trous, et le piège des intervalles imbriqués."""
from __future__ import annotations

from outils_ia.audit.gen_trous_livre import trouver_trous


class _M:
    """Marqueur minimal : le détecteur n'a besoin que de ces cinq champs."""

    def __init__(self, l1, l2, notion, chap="III", phys=149):
        self.l1, self.l2, self.notion = l1, l2, notion
        self.chap, self.phys = chap, phys


def test_un_intervalle_imbrique_ne_fabrique_PAS_de_trou():
    """🎯 LE BUG DU 19 AOÛT, et il valait 15 trous fantômes sur 175.

    Sur E III.46, les marqueurs L.14-20, L.15-16, L.19-19 et L.21-24 faisaient
    signaler des trous L.17-18 et L.20-20 — tous deux À L'INTÉRIEUR de L.14-20.
    Cause : l'algorithme comparait chaque marqueur au SUIVANT (`zip(g, g[1:])`)
    au lieu de suivre le MAXIMUM COURANT des bornes hautes. Une page finement
    annotée était donc punie de l'être."""
    ms = [_M(14, 20, "c62"), _M(15, 16, "bon_ordre"),
          _M(19, 19, "domaine"), _M(21, 24, "c63")]
    assert trouver_trous(ms) == []


def test_un_vrai_trou_est_toujours_signale():
    """La correction ne doit pas rendre le détecteur aveugle."""
    trous = trouver_trous([_M(1, 5, "a"), _M(9, 12, "b")])
    assert len(trous) == 1
    _chap, _phys, g1, g2, avant, apres = trous[0]
    assert (g1, g2, avant, apres) == (6, 8, "a", "b")


def test_le_trou_est_attribue_au_marqueur_qui_couvre_le_plus_loin():
    """Après un imbriqué, le « avant » du trou doit être le marqueur qui tient
    réellement la borne — sinon le rapport désigne la mauvaise notion."""
    trous = trouver_trous([_M(1, 20, "large"), _M(3, 4, "petit"), _M(30, 33, "suivant")])
    assert len(trous) == 1
    _c, _p, g1, g2, avant, apres = trous[0]
    assert (g1, g2, avant, apres) == (21, 29, "large", "suivant")


def test_la_contiguite_n_est_pas_un_trou():
    """L.1-5 puis L.6-9 : rien entre les deux."""
    assert trouver_trous([_M(1, 5, "a"), _M(6, 9, "b")]) == []


def test_deux_pages_differentes_ne_se_melangent_pas():
    """Un trou ne se calcule qu'à l'intérieur d'une même page physique."""
    ms = [_M(1, 5, "a", phys=100), _M(40, 44, "b", phys=101)]
    assert trouver_trous(ms) == []
