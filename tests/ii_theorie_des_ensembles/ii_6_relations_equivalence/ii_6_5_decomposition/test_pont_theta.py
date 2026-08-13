# -*- coding: utf-8 -*-
"""Tests — le PONT b(θ(x))=f(x) DÉMONTRÉ, et la décomposition canonique déchargée."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_pont_theta import (
    pont_au_point, pont_demontre, b_construite_injective, b_construite_surjective,
)


def test_pont_au_point():
    """{x∈E, θ(x)∈Q} ⊢ b(θ(x)) = f(x) — b CONSTRUIT, sans section."""
    assert len(pont_au_point().hypotheses) == 2


def test_pont_demontre():
    """🎯 Le PONT (hypothèse de b_injective_via_pont) est DÉMONTRÉ — 1 hyp."""
    assert len(pont_demontre().hypotheses) == 1


def test_b_construite_injective():
    """👑 Injectivité de la bijection induite, pont déchargé — 1 hyp."""
    assert len(b_construite_injective().hypotheses) == 1


def test_b_construite_surjective():
    """👑 Surjectivité sur f⟨E⟩, pont déchargé — 2 hyps ; theorie==22."""
    assert len(b_construite_surjective().hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22
