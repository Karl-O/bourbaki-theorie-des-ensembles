# -*- coding: utf-8 -*-
"""Tests — CST1 GÉNÉRÉ (le métathéorème par schéma concret).  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, schema_parties, schema_produit, schema_relation,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    cst1_termes_prouve,
)


def _run(s, n):
    fs = [f"f{i}" for i in range(1, n + 1)]
    gs = [f"g{i}" for i in range(1, n + 1)]
    bs = [f"Eb{i}" for i in range(1, n + 1)]
    bp = [f"Ep{i}" for i in range(1, n + 1)]
    bpp = [f"Epp{i}" for i in range(1, n + 1)]
    return cst1_termes_prouve(s, fs, gs, bs, bp, bpp)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_cst1_parties():
    """Schéma 𝔓E : 1 hyp (borne-image)."""
    th, hyps = _run(schema_parties(), 1)
    assert len(hyps) == 1 and set(th.hypotheses) <= set(hyps)


def test_cst1_produit():
    """Schéma E₁×E₂ : 4 hyps est_application."""
    th, hyps = _run(schema_produit(), 2)
    assert len(hyps) == 4 and set(th.hypotheses) <= set(hyps)


def test_cst1_relation():
    """🎯 Schéma relationnel 𝔓(E×E) — 3 étages, × puis 𝔓 : 3 hyps."""
    th, hyps = _run(schema_relation(), 1)
    assert len(hyps) == 3 and set(th.hypotheses) <= set(hyps)
    assert th.conclusion not in th.hypotheses


def test_cst1_profond():
    """🎯🎯 Schéma 𝔓(𝔓(E×E)) — récurrence à 4 étages : le générateur RÉCURSE."""
    th, hyps = _run(Schema(((0, 1), (1, 1), (2, 0), (3, 0))), 1)
    assert len(hyps) == 4 and set(th.hypotheses) <= set(hyps)
    assert len(E.theorie_ensembles().axiomes) == 22
