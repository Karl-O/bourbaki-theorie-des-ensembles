"""Tests V9 — §II.6.6 : R_A transitive et R_A relation d'équivalence (héritées de R).

Vérifient, pour chaque théorème : conclusion EXACTE (== cible reconstruite via
`ensembles_abrege`) + hypothèses HONNÊTES exactes (jamais la conclusion).
theorie_ensembles reste à 22 axiomes.
"""
from __future__ import annotations

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_6_equivalence.ii_6_6_relation_induite import (
    ensembles_relation_induite_equivalence as RI)


# ════════════════════════════════════════════════════════════════════════════
# theorie_ensembles reste à 22 axiomes (aucun axiome neuf)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
# Théorème 1 — R_A transitive   {R transitive}
# ════════════════════════════════════════════════════════════════════════════
def test_relation_induite_transitive():
    """{R transitive} ⊢ R_A transitive  (E.II.6.6 ; clos mod. hyp.)."""
    R = E.rel_graphe("GR")
    t = RI.relation_induite_transitive(R, "A")
    # conclusion == est_transitive(R_A) (cible reconstruite)
    assert t.conclusion == RI.relation_induite_transitive_cible(R, "A")
    # hypothèse honnête = transitivité de R seule
    assert t.hypotheses == frozenset({E.est_transitive(R, "a", "b", "c")})


# ════════════════════════════════════════════════════════════════════════════
# Théorème 2 — R_A relation d'équivalence   {R symétrique, R transitive}
# ════════════════════════════════════════════════════════════════════════════
def test_relation_induite_relation_equivalence():
    """{R symétrique, R transitive} ⊢ R_A relation d'équivalence  (E.II.6.6 ; clos mod. hyp.)."""
    R = E.rel_graphe("GR")
    t = RI.relation_induite_relation_equivalence(R, "A")
    # conclusion == est_relation_equivalence(R_A) (= symétrie ET transitivité)
    assert t.conclusion == RI.relation_induite_relation_equivalence_cible(R, "A")
    # hypothèses honnêtes = symétrie + transitivité de R (jamais la conclusion)
    assert t.hypotheses == frozenset({
        E.est_symetrique(R, "x", "y"),
        E.est_transitive(R, "a", "b", "c"),
    })
