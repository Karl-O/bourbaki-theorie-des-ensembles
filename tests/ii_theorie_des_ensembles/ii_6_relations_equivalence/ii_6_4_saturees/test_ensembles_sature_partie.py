"""Test miroir — §II.6.4 : l'image réciproque p⁻¹⟨B⟩ est saturée pour R.

Théorème CONDITIONNEL (salvage fort) : on vérifie que les HYPOTHÈSES sont
EXACTEMENT les prémisses explicites attendues (anti-affaibli : ni plus, ni moins)
ET que la conclusion est la cible Bourbaki est_saturee(p⁻¹⟨B⟩, G) (anti-tautologie :
conclusion ∉ hypothèses).  theorie_ensembles() == 22 (intangible).
"""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_4_saturees.ensembles_sature_partie import (
    relation_dans, cible_sature_partie_saturee, sature_partie_saturee,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── le cœur : conclusion == cible, hypothèses exactes, anti-tautologie ────────
def test_sature_partie_saturee_conclusion_et_hypotheses():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    th = sature_partie_saturee()
    G = var("G")
    Rg = E.rel_graphe(G)

    # conclusion == est_saturee(p⁻¹⟨B⟩, G)  (cible Bourbaki, liants x, y)
    assert th.conclusion == cible_sature_partie_saturee()

    # hypothèses == {R sym, R trans, G relation dans E}  (exactement)
    attendues = frozenset({
        E.est_symetrique(Rg, "p", "q"),          # R symétrique
        E.est_transitive(Rg, "p", "q", "r"),     # R transitive
        relation_dans(G, var("E")),              # G relation dans E : (∀a)(∀b)((a,b)∈G ⇒ b∈E)
    })
    assert th.hypotheses == attendues

    # anti-tautologie : la conclusion n'est pas une simple hypothèse
    assert th.conclusion not in th.hypotheses


def test_sature_partie_saturee_primitives_only():
    """Le théorème sort du noyau abrégé (aucun Theoreme fabriqué) : on vérifie
    simplement qu'il se reconstruit identique (déterminisme du noyau)."""
    a = sature_partie_saturee()
    b = sature_partie_saturee()
    assert a.conclusion == b.conclusion
    assert a.hypotheses == b.hypotheses
