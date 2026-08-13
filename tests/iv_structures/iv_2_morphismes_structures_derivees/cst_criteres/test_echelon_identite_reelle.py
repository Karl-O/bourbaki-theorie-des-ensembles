# -*- coding: utf-8 -*-
"""Tests — T5 réel : ⟨Δ⟩^S_réel bijection de S(E) sur S(E), CLOS.  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    Schema, schema_parties, schema_relation,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_echelon_identite_reelle import (
    echelon_identite_bijection_reelle,
)


def test_t5_parties_close():
    """Schéma 𝔓E : bij(⟨Δ⟩^𝔓, 𝔓E, 𝔓E), CLOS — les 2 hyps de l'opaque déchargées."""
    assert echelon_identite_bijection_reelle(schema_parties(), ["Eb1"]).est_clos


def test_t5_relation_close():
    """🎯 Schéma relationnel 𝔓(E×E), CLOS."""
    assert echelon_identite_bijection_reelle(schema_relation(), ["Eb1"]).est_clos


def test_t5_profond_close():
    """🎯🎯 Schéma 𝔓(𝔓(E×E)) — 4 étages, CLOS ; theorie==22."""
    th = echelon_identite_bijection_reelle(
        Schema(((0, 1), (1, 1), (2, 0), (3, 0))), ["Eb1"])
    assert th.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22
