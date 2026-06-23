"""Tests §II.4.2 — ASSOCIATIVITÉ de la réunion (Prop. 2, partie inconditionnelle).

Vérifie : conclusion EXACTE (== cible verbatim = égalité des deux réunions),
hypothèses = EXACTEMENT les 2 clauses (couverture ∧ domaine, jamais la conclusion,
jamais d'hypothèse parasite), et theorie_ensembles() reste à 22 axiomes (l'axiome de
valeur de la famille interne G vit dans une théorie séparée, pas en principale).
"""
from bourbaki.logique.i_1_termes_relations.formule import (var, et, impl, appartient,
                                       existe, pourtout)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_1_definitions_algebre import ensembles_familles_assoc_reunion as A


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_associativite_reunion_famille():
    vx, vj, vL = var("X"), var("J"), var("L")
    vi, vl = var("i"), var("l")
    G = A.famille_assoc(vx, vj)

    cible = A.cible()
    # cible == égalité des deux réunions
    from bourbaki.logique.i_1_termes_relations.formule import egal
    assert cible == egal(E.reunion_famille(vx, vL), E.reunion_famille(G, vL))

    t = A.associativite_reunion_famille()
    # conclusion == cible verbatim
    assert t.conclusion == cible

    # hypothèses = EXACTEMENT les 2 clauses (couverture) et (domaine), séparées
    Jl = E.valeur_famille(vj, vl)
    couverture = pourtout("i", impl(appartient(vi, vL),
        existe("l", et(appartient(vl, vL), appartient(vi, Jl)))))
    domaine = pourtout("l", pourtout("i",
        impl(et(appartient(vl, vL), appartient(vi, Jl)), appartient(vi, vL))))
    assert t.hypotheses == frozenset({couverture, domaine})

    # non vacuité : la conclusion n'est pas elle-même une hypothèse
    assert t.conclusion not in t.hypotheses
    # le théorème n'est PAS clos (il est conditionné aux 2 clauses)
    assert not t.est_clos
