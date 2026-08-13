"""Tests V9 — §II.6.6 : S∘φ relation d'équivalence et (S∘φ)_E réflexive dans E.

Vérifient, pour chaque théorème : conclusion EXACTE (== cible reconstruite via
`ensembles_abrege`) + hypothèses HONNÊTES exactes (jamais la conclusion).
theorie_ensembles reste à 22 axiomes.
"""
from __future__ import annotations

from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, impl, appartient, pourtout
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_6_relation_induite import (
    ensembles_image_reciproque_reflexive as IR)


# ════════════════════════════════════════════════════════════════════════════
# theorie_ensembles reste à 22 axiomes (aucun axiome neuf)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
# Théorème 1 — S∘φ relation d'équivalence   {S symétrique, S transitive}
# ════════════════════════════════════════════════════════════════════════════
def test_image_reciproque_relation_equivalence():
    """{S symétrique, S transitive} ⊢ S∘φ relation d'équivalence  (E.II.6.6 ; clos mod. hyp.)."""
    S = E.rel_graphe("GS")
    t = IR.image_reciproque_relation_equivalence(S, "phi")
    # conclusion == est_relation_equivalence(S∘φ) (= symétrie ET transitivité)
    assert t.conclusion == IR.image_reciproque_relation_equivalence_cible(S, "phi")
    # hypothèses honnêtes = symétrie + transitivité de S (jamais la conclusion)
    assert t.hypotheses == frozenset({
        E.est_symetrique(S, "a", "b"),
        E.est_transitive(S, "a", "b", "c"),
    })


# ════════════════════════════════════════════════════════════════════════════
# Théorème 2 — (S∘φ)_E réflexive dans E   {S réflexive dans F, φ:E→F}
# ════════════════════════════════════════════════════════════════════════════
def test_image_reciproque_reflexive():
    """{S réflexive dans F, φ:E→F} ⊢ (S∘φ)_E réflexive dans E  (E.II.6.6 ; clos mod. hyp.)."""
    S = E.rel_graphe("GS")
    t = IR.image_reciproque_reflexive(S, "phi", "E", "F")
    # conclusion == est_reflexive_dans((S∘φ)_E, E) = (∀x)((S∘φ)_E{x,x} ⇔ x∈E)
    assert t.conclusion == IR.image_reciproque_reflexive_cible(S, "phi", "E")
    # hypothèses honnêtes = réflexivité de S dans F + φ:E→F (jamais la conclusion)
    vx, vphi, ve, vf = var("x"), var("phi"), var("E"), var("F")
    hypo_phi = pourtout("x", impl(appartient(vx, ve),
                                  appartient(E.valeur(vphi, vx), vf)))
    assert t.hypotheses == frozenset({
        E.est_reflexive_dans(S, vf, "x"),
        hypo_phi,
    })
