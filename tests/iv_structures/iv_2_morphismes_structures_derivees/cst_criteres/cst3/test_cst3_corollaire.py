# -*- coding: utf-8 -*-
"""Tests — corollaire CST3 : f⁻¹∘f=Δ_A et ⟨f⁻¹⟩^S∘⟨f⟩^S=Δ_{S(E)}."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    schema_parties, schema_relation,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_corollaire import (
    composee_reciproque_diagonale, cst3_corollaire_identite,
)


def test_base_composee_reciproque():
    """{dom f=A, func f⁻¹} ⊢ f⁻¹∘f = Δ_A — 2 hyps ⊆ Q(f)."""
    assert len(composee_reciproque_diagonale("f", "A").hypotheses) == 2


def test_capstone_relation():
    """🎯🎯 ⟨f⁻¹⟩^S ∘ ⟨f⟩^S = Δ_{S(E)} sur 𝔓(E×E) ; theorie==22."""
    th, hy = cst3_corollaire_identite(schema_relation(), ["f1"], ["Eb1"], ["Ep1"])
    assert set(th.hypotheses) <= set(hy)
    th, hy = cst3_corollaire_identite(schema_parties(), ["f1"], ["Eb1"], ["Ep1"])
    assert set(th.hypotheses) <= set(hy)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_valeur_reciproque_identite():
    """👑 ⟨f⁻¹⟩^S(⟨f⟩^S(U)) = U — la 3e hyp des consommateurs iso, déchargée."""
    from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_cst3_corollaire import (
        valeur_reciproque_identite,
    )
    th, hy = valeur_reciproque_identite(schema_relation(), ["f1"], ["Eb1"], ["Ep1"])
    assert set(th.hypotheses) <= set(hy)
    assert len(E.theorie_ensembles().axiomes) == 22
