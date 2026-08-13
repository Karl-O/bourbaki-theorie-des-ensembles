"""Test miroir — §II.6.4 : stabilité d'une FAMILLE de parties saturées (E.II.43).

Théorèmes CONDITIONNELS (salvage fort) : on APPELLE chaque fonction, on vérifie que
la conclusion == la cible Bourbaki est_saturee(⋃X_ι, G) / est_saturee(⋂X_ι, G)
RECONSTRUITE avec E.est_saturee (même forme, liants x, y), et que les HYPOTHÈSES
sont EXACTEMENT {(∀i)(i∈I ⇒ est_saturee(X_i, G))} (anti-affaibli : ni plus, ni
moins ; anti-tautologie : conclusion ∉ hypothèses).  theorie_ensembles() == 22.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, impl, appartient, pourtout)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_4_saturees.ensembles_saturees_famille import (
    cible_reunion_famille_saturee, cible_inter_famille_saturee,
    famille_de_saturees_reunion, famille_de_saturees_inter,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def _hyp_famille_attendue():
    X, I, G = var("X"), var("I"), var("G")
    vi = var("i")
    Xi = E.valeur_famille(X, vi)
    # (∀i)(i∈I ⇒ est_saturee(X_i, G))  — reconstruite indépendamment, liant i
    return frozenset({
        pourtout("i", impl(appartient(vi, I),
                           E.est_saturee(Xi, G, Xi, x="x"))),
    })


def test_reunion_conclusion_et_hypotheses():
    th = famille_de_saturees_reunion()
    # conclusion == est_saturee(⋃X_ι, G)  (cible Bourbaki, liants x, y)
    assert th.conclusion == cible_reunion_famille_saturee()
    # hypothèses == {(∀i)(i∈I ⇒ est_saturee(X_i,G))}  (exactement)
    assert th.hypotheses == _hyp_famille_attendue()
    # anti-tautologie : la conclusion n'est pas une simple hypothèse
    assert th.conclusion not in th.hypotheses


def test_inter_conclusion_et_hypotheses():
    th = famille_de_saturees_inter()
    assert th.conclusion == cible_inter_famille_saturee()
    assert th.hypotheses == _hyp_famille_attendue()
    assert th.conclusion not in th.hypotheses


def test_determinisme():
    """Le noyau est déterministe : reconstruction identique (aucun Theoreme fabriqué)."""
    for f in (famille_de_saturees_reunion, famille_de_saturees_inter):
        a, b = f(), f()
        assert a.conclusion == b.conclusion
        assert a.hypotheses == b.hypotheses
