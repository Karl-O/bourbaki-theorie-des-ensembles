"""Tests §II.4.2 — ASSOCIATIVITÉ de l'intersection (Prop. 2, 2e formule).

Vérifie : conclusion EXACTE (== cible verbatim = égalité des deux intersections),
hypothèses = EXACTEMENT les 3 clauses (couverture ∧ domaine ∧ non-vacuité, jamais la
conclusion, jamais d'hypothèse parasite), et theorie_ensembles() reste à 22 axiomes
(l'axiome de valeur de la famille interne G vit dans une théorie séparée).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, impl, appartient,
                                       existe, pourtout)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_2_proprietes import ensembles_familles_assoc_inter as A


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_associativite_inter_famille():
    vx, vj, vL = var("X"), var("J"), var("L")
    vi, vl = var("i"), var("l")
    G = A.famille_assoc_inter(vx, vj)

    cible = A.cible()
    # cible == égalité des deux intersections
    assert cible == egal(E.inter_famille(vx, vL), E.inter_famille(G, vL))

    t = A.associativite_inter_famille()
    # conclusion == cible verbatim
    assert t.conclusion == cible

    # hypothèses = EXACTEMENT les 3 clauses (a) couverture, (b) domaine, (c) non-vacuité
    Jl = E.valeur_famille(vj, vl)
    couverture = pourtout("i", impl(appartient(vi, vL),
        existe("l", et(appartient(vl, vL), appartient(vi, Jl)))))
    domaine = pourtout("l", pourtout("i",
        impl(et(appartient(vl, vL), appartient(vi, Jl)), appartient(vi, vL))))
    non_vacuite = pourtout("l", impl(appartient(vl, vL),
        existe("i", appartient(vi, Jl))))
    assert t.hypotheses == frozenset({couverture, domaine, non_vacuite})

    # non vacuité : la conclusion n'est pas elle-même une hypothèse
    assert t.conclusion not in t.hypotheses
    # le théorème n'est PAS clos (il est conditionné aux 3 clauses)
    assert not t.est_clos
    # theorie principale toujours à 22 (famille interne G en théorie séparée)
    assert len(E.theorie_ensembles().axiomes) == 22
