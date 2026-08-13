# -*- coding: utf-8 -*-
"""Tests — CST2 : étage ×, générateur, pont est_bijection_de.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, schema_parties, schema_produit, schema_relation, construction_echelon,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_genere import (
    extension_canonique_reelle,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_etage_produit import (
    produit_app_bijective_q,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst2.ensembles_cst2_genere import (
    cst2_prouve, pont_bijection_de,
)


def test_etage_produit():
    """🎯 8 hyps honnêtes = Q(f)∖dom ∪ Q(g)∖dom."""
    th = produit_app_bijective_q("f", "g", "A", "B", "Ap", "Bp")
    assert len(th.hypotheses) == 8


def test_cst2_produit():
    """Schéma E₁×E₂ : hyps = les 2 Q(f_i), rien d'autre."""
    th, hy = cst2_prouve(schema_produit(), ["f1", "f2"],
                         ["Eb1", "Eb2"], ["Ep1", "Ep2"])
    assert len(hy) == 2 and set(th.hypotheses) <= set(hy)


def test_cst2_relation():
    """🎯 Schéma 𝔓(E×E) : une seule hyp résiduelle Q(f₁)."""
    th, hy = cst2_prouve(schema_relation(), ["f1"], ["Eb1"], ["Ep1"])
    assert len(hy) == 1 and set(th.hypotheses) <= set(hy)


def test_cst2_profond_et_pont():
    """🎯🎯 𝔓(𝔓(E×E)) 4 étages + pont vers est_bijection_de (E III.3.1)."""
    s = Schema(((0, 1), (1, 1), (2, 0), (3, 0)))
    th, hy = cst2_prouve(s, ["f1"], ["Eb1"], ["Ep1"])
    assert len(hy) == 1
    G = extension_canonique_reelle(s, [var("f1")], ["Eb1"])
    A = construction_echelon(s, [var("Eb1")])
    Ap = construction_echelon(s, [var("Ep1")])
    pb = pont_bijection_de(th, G[-1], A[-1], Ap[-1])
    assert set(pb.hypotheses) <= set(hy)
    assert len(E.theorie_ensembles().axiomes) == 22
