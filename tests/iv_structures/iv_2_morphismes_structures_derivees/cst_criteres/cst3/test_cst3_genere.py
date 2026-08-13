# -*- coding: utf-8 -*-
"""Tests — CST3 : étages 𝔓/×, générateur réciprocité.  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, schema_produit, schema_relation,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_etage_parties import (
    reciproque_ext_parties,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_etage_produit import (
    reciproque_produit_app,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_genere import (
    cst3_prouve,
)


def test_etage_parties():
    """(ext_P g)⁻¹ = ext_P(g⁻¹) — 4 hyps honnêtes Q(g)∖dom."""
    assert len(reciproque_ext_parties("g", "A", "Ap").hypotheses) == 4


def test_etage_produit():
    """(f×g)⁻¹ = f⁻¹×g⁻¹ — 8 hyps honnêtes."""
    assert len(reciproque_produit_app("f", "g", "A", "B", "Ap", "Bp").hypotheses) == 8


def test_cst3_produit_et_relation():
    """🎯 hyps résiduelles = exactement les n Q(f_i)."""
    th, hy = cst3_prouve(schema_produit(), ["f1", "f2"],
                         ["Eb1", "Eb2"], ["Ep1", "Ep2"])
    assert len(hy) == 2 and set(th.hypotheses) <= set(hy)
    th, hy = cst3_prouve(schema_relation(), ["f1"], ["Eb1"], ["Ep1"])
    assert len(hy) == 1 and set(th.hypotheses) <= set(hy)


def test_cst3_profond():
    """🎯🎯 𝔓(𝔓(E×E)) — 4 étages, double fil Q+réciproque ; theorie==22."""
    th, hy = cst3_prouve(Schema(((0, 1), (1, 1), (2, 0), (3, 0))),
                         ["f1"], ["Eb1"], ["Ep1"])
    assert len(hy) == 1 and set(th.hypotheses) <= set(hy)
    assert len(E.theorie_ensembles().axiomes) == 22
