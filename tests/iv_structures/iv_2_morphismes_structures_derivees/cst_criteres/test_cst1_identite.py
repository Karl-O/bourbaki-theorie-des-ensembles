# -*- coding: utf-8 -*-
"""Tests — CST1-IDENTITÉ GÉNÉRÉ : ⟨Δ⟩^S = Δ_{S(E)}, CLOS.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, schema_parties, schema_produit, schema_relation,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst1_identite import (
    image_diagonale_sous, identite_parties, identite_produit, cst1_identite_prouve,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_image_diagonale_sous():
    """(i) {pt∈𝔓A} ⊢ Δ_A⟨pt⟩ = pt — la seule pièce à hypothèse (honnête)."""
    th = image_diagonale_sous(var("A"))
    assert len(th.hypotheses) == 1


def test_identite_parties_close():
    """(ii) ext_P(Δ_A, A) = Δ_𝔓A, CLOS."""
    assert identite_parties(var("A")).est_clos


def test_identite_produit_close():
    """(iii) prod(Δ_A, Δ_B, A, B) = Δ_{A×B}, CLOS."""
    assert identite_produit(var("A"), var("B")).est_clos


def test_cst1_identite_relation():
    """🎯 (iv) schéma relationnel 𝔓(E×E) : ⟨Δ⟩^S = Δ_{S(E)}, CLOS."""
    assert cst1_identite_prouve(schema_relation(), ["Eb1"]).est_clos


def test_cst1_identite_profond():
    """🎯🎯 (iv) schéma 𝔓(𝔓(E×E)) — 4 étages, le générateur RÉCURSE, CLOS."""
    th = cst1_identite_prouve(Schema(((0, 1), (1, 1), (2, 0), (3, 0))), ["Eb1"])
    assert th.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22
