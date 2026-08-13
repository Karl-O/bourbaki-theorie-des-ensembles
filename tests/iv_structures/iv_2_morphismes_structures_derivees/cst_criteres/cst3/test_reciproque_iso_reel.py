# -*- coding: utf-8 -*-
"""Tests — réversion d'isomorphisme réelle (IV.1.5, toutes hyps CST déchargées)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    schema_parties, schema_relation,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_reciproque_iso_reel import (
    bijection_reciproque, reciproque_isomorphisme_reel,
)


def test_bijection_reciproque():
    """{4 conjoints Q} ⊢ est_bijection_de(G⁻¹, Y, X) — générique."""
    assert len(bijection_reciproque("g", "X", "Y").hypotheses) == 4


def test_reciproque_iso_reel():
    """👑 bij((⟨f⟩^S)⁻¹) ∧ (⟨f⟩^S)⁻¹(V)=U — hyps = Q(f)+bornes+{U∈S(E), ⟨f⟩(U)=V}."""
    th, hy = reciproque_isomorphisme_reel(schema_relation(), ["f1"], ["Eb1"], ["Ep1"])
    assert set(th.hypotheses) <= set(hy)
    th, hy = reciproque_isomorphisme_reel(schema_parties(), ["f1"], ["Eb1"], ["Ep1"])
    assert set(th.hypotheses) <= set(hy)
    assert len(E.theorie_ensembles().axiomes) == 22
