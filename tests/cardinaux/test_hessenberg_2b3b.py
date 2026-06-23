"""Tests — §III.6.3 sous-pièces arithmétiques 2𝔟=𝔟 / 3𝔟=𝔟 (ensembles_hessenberg_2b3b).

deux_b_egal_b / trois_b_egal_b : égalités cardinales par ANTISYMÉTRIE, sous les
hypothèses HONNÊTES (est_cardinal(𝔟) et la descente 2𝔟≤𝔟 / 3𝔟≤𝔟 — verrou « n≤𝔟 »
REPORTÉ).  Le ≥ est inconditionnel et clos ; rien postulé ; theorie=22.
"""
from bourbaki.logique.formule import var, egal, et
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, inf_egal_card, est_cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.ensembles_hessenberg_2b3b import deux_b_egal_b, trois_b_egal_b


def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── deux_b_egal_b : 2𝔟 = 𝔟 ───────────────────────────────────────────────────
def test_deux_b_egal_b_conclusion():
    vb = var("b")
    t = deux_b_egal_b("b")
    bplusb = somme_cardinale_binaire(vb, vb)
    assert t.conclusion == egal(bplusb, vb)


def test_deux_b_egal_b_hyps_honnetes():
    vb = var("b")
    t = deux_b_egal_b("b")
    bplusb = somme_cardinale_binaire(vb, vb)
    # exactement les 2 hyps honnêtes
    assert est_cardinal(vb) in t.hypotheses
    assert inf_egal_card(bplusb, vb) in t.hypotheses
    assert len(t.hypotheses) == 2
    # NON vacuous : la conclusion n'est pas dans les hyps
    assert t.conclusion not in t.hypotheses


# ── trois_b_egal_b : 3𝔟 = 𝔟 ──────────────────────────────────────────────────
def test_trois_b_egal_b_conclusion():
    vb = var("b")
    t = trois_b_egal_b("b")
    bb = somme_disjointe(vb, vb)
    threeb = somme_cardinale_binaire(vb, bb)
    assert t.conclusion == egal(threeb, vb)


def test_trois_b_egal_b_hyps_honnetes():
    vb = var("b")
    t = trois_b_egal_b("b")
    bb = somme_disjointe(vb, vb)
    threeb = somme_cardinale_binaire(vb, bb)
    assert est_cardinal(vb) in t.hypotheses
    assert inf_egal_card(threeb, vb) in t.hypotheses
    assert len(t.hypotheses) == 2
    assert t.conclusion not in t.hypotheses


# ── ré-instanciation sur une autre VARIABLE ──────────────────────────────────
def test_deux_b_egal_b_autre_var():
    va = var("a")
    t = deux_b_egal_b("a")
    assert t.conclusion == egal(somme_cardinale_binaire(va, va), va)
    assert len(t.hypotheses) == 2
