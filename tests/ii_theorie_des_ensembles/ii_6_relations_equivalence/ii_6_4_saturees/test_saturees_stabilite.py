"""Test miroir — §II.6.4 : stabilité des parties saturées par ∪ et ∩ (E.II.43).

Théorèmes CONDITIONNELS (salvage fort) : on APPELLE chaque fonction, on vérifie que
la conclusion == la cible Bourbaki est_saturee(A∪B, G) / est_saturee(A∩B, G)
RECONSTRUITE avec E.est_saturee (même forme, liants x, y), et que les HYPOTHÈSES
sont EXACTEMENT {est_saturee(A,G), est_saturee(B,G)} (anti-affaibli : ni plus, ni
moins ; anti-tautologie : conclusion ∉ hypothèses).  theorie_ensembles() == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_4_saturees.ensembles_sature_partie import (
    relation_dans,
)
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_4_saturees.ensembles_saturees_stabilite import (
    cible_reunion_saturee, cible_intersection_saturee,
    reunion_de_saturees_est_saturee, intersection_de_saturees_est_saturee,
    cible_complementaire_saturee, complementaire_de_saturee_est_saturee,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def _hyps_attendues():
    A, B, G = var("A"), var("B"), var("G")
    return frozenset({
        E.est_saturee(A, G, A, x="x"),    # A saturée pour R
        E.est_saturee(B, G, B, x="x"),    # B saturée pour R
    })


def test_reunion_conclusion_et_hypotheses():
    th = reunion_de_saturees_est_saturee()
    # conclusion == est_saturee(A∪B, G)  (cible Bourbaki, liants x, y)
    assert th.conclusion == cible_reunion_saturee()
    # hypothèses == {est_saturee(A,G), est_saturee(B,G)}  (exactement)
    assert th.hypotheses == _hyps_attendues()
    # anti-tautologie : la conclusion n'est pas une simple hypothèse
    assert th.conclusion not in th.hypotheses


def test_intersection_conclusion_et_hypotheses():
    th = intersection_de_saturees_est_saturee()
    assert th.conclusion == cible_intersection_saturee()
    assert th.hypotheses == _hyps_attendues()
    assert th.conclusion not in th.hypotheses


def _hyps_complementaire_attendues():
    A, E_, G = var("A"), var("E"), var("G")
    return frozenset({
        E.est_saturee(A, G, A, x="x"),                 # A saturée pour R
        E.est_symetrique(E.rel_graphe(G), "a", "b"),   # G symétrique (graphe)
        relation_dans(G, E_),                          # G relation dans E
    })


def test_complementaire_conclusion_et_hypotheses():
    th = complementaire_de_saturee_est_saturee()
    # conclusion == est_saturee(E∖A, G)  (cible Bourbaki, liants x, y)
    assert th.conclusion == cible_complementaire_saturee()
    # hypothèses == {A saturée, G symétrique, G relation dans E}  (exactement)
    assert th.hypotheses == _hyps_complementaire_attendues()
    # anti-tautologie : la conclusion n'est pas une simple hypothèse
    assert th.conclusion not in th.hypotheses


def test_determinisme():
    """Le noyau est déterministe : reconstruction identique (aucun Theoreme fabriqué)."""
    for f in (reunion_de_saturees_est_saturee, intersection_de_saturees_est_saturee,
              complementaire_de_saturee_est_saturee):
        a, b = f(), f()
        assert a.conclusion == b.conclusion
        assert a.hypotheses == b.hypotheses
