"""Tests — §II.6.1 Proposition 1 (sens réciproque) : conditions sur le graphe G.

Vérifie (noyau LCF strict) pour les volets (b) symétrie, (c) transitivité et leur
assemblage en condition d'équivalence (`est_relation_equivalence`, E.II.6.1) :
  • chaque théorème BUILD (pas d'exception du noyau) et est CLOS modulo hypothèses ;
  • non VACUEUX : conclusion ∉ hypothèses ;
  • CONCLUSION littéralement la cible Bourbaki (est_symetrique / est_transitive /
    est_relation_equivalence de rel_graphe(G)) ;
  • HYPOTHÈSES = exactement les antécédents honnêtes load-bearing
    ({G = G⁻¹} ; {G∘G ⊂ G} ; {G = G⁻¹, G∘G ⊂ G}) — jamais la conclusion en hyp ;
  • theorie_ensembles() RESTE à 22 axiomes (aucun axiome neuf).
"""
from __future__ import annotations

import bourbaki.ensembles.ii_6_equivalence.ensembles_proposition1_gamma as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var, egal, inclus


def _R():
    return E.rel_graphe("G")


def _G():
    return var("G")


def _h_egal():
    """G = G⁻¹."""
    g = _G()
    return egal(g, E.reciproque(g))


def _h_incl():
    """G∘G ⊂ G."""
    g = _G()
    return inclus(E.composee(g, g), g)


def _non_vacuous(thm):
    assert thm.conclusion not in thm.hypotheses, "VACUEUX : conclusion ∈ hypothèses"


# ── theorie inchangée ─────────────────────────────────────────────────────────
def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── cibles ────────────────────────────────────────────────────────────────────
def test_cibles():
    assert M.cible_symetrique("G") == E.est_symetrique(_R())
    assert M.cible_transitive("G") == E.est_transitive(_R())
    assert M.cible_equivalence("G") == E.est_relation_equivalence(_R())


# ── (b) symétrie : {G = G⁻¹} ⊢ est_symetrique(R) ──────────────────────────────
def test_gamma_symetrique():
    t = M.gamma_symetrique_si_egal_reciproque("G")
    _non_vacuous(t)
    assert t.conclusion == E.est_symetrique(_R())
    assert t.conclusion == M.cible_symetrique("G")
    # séquent : exactement {G = G⁻¹}
    assert _h_egal() in t.hypotheses
    assert _h_incl() not in t.hypotheses
    assert len(t.hypotheses) == 1


# ── (c) transitivité : {G∘G ⊂ G} ⊢ est_transitive(R) ──────────────────────────
def test_gamma_transitive():
    t = M.gamma_transitive_si_composee_incluse("G")
    _non_vacuous(t)
    assert t.conclusion == E.est_transitive(_R())
    assert t.conclusion == M.cible_transitive("G")
    # séquent : exactement {G∘G ⊂ G}
    assert _h_incl() in t.hypotheses
    assert _h_egal() not in t.hypotheses
    assert len(t.hypotheses) == 1


# ── assemblage : {G = G⁻¹, G∘G ⊂ G} ⊢ est_relation_equivalence(R) ─────────────
def test_prop1_reciproque_equivalence():
    t = M.prop1_reciproque_equivalence("G")
    _non_vacuous(t)
    # conclusion littéralement la cible
    assert t.conclusion == E.est_relation_equivalence(_R())
    assert t.conclusion == M.cible_equivalence("G")
    # séquent : exactement {G = G⁻¹, G∘G ⊂ G} (les deux antécédents honnêtes)
    assert _h_egal() in t.hypotheses
    assert _h_incl() in t.hypotheses
    assert len(t.hypotheses) == 2


# ── théorie toujours intacte après usage ───────────────────────────────────────
def test_theorie_22_apres_usage():
    M.prop1_reciproque_equivalence()
    assert len(E.theorie_ensembles().axiomes) == 22
