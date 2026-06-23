"""Tests §II.2 — distributivité du produit cartésien (cœur de A×(B∪C)=(A×B)∪(A×C)
et A×(B∩C)=(A×B)∩(A×C)), au niveau de l'appartenance d'un couple.

Vérifie (honnêteté LCF stricte) : CLÔTURE (0 hyp), conclusion == l'ÉQUIVALENCE FIDÈLE
littérale entre les deux appartenances, NON-VACUITÉ (les deux membres DIFFÈRENT), et
theorie_ensembles() = 22.
"""
from bourbaki.logique.formule import var, equiv, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
import bourbaki.ensembles.ii_2_couples_produit.ensembles_produit_distributif as M


def _couple_in(prod):
    return appartient(E.couple(var("u"), var("v")), prod)


def test_distributif_reunion_clos_et_fidele():
    t = M.couple_dans_produit_distributif_reunion()
    assert t.est_clos and not t.hypotheses
    lhs = _couple_in(E.produit(var("A"), E.reunion(var("B"), var("C"))))         # (u,v)∈A×(B∪C)
    rhs = _couple_in(E.reunion(E.produit(var("A"), var("B")),
                               E.produit(var("A"), var("C"))))                    # (u,v)∈(A×B)∪(A×C)
    assert t.conclusion == equiv(lhs, rhs)         # ÉNONCÉ FIDÈLE LITTÉRAL
    assert lhs != rhs                               # NON vacueux (membres distincts)


def test_distributif_intersection_clos_et_fidele():
    t = M.couple_dans_produit_distributif_intersection()
    assert t.est_clos and not t.hypotheses
    lhs = _couple_in(E.produit(var("A"), E.intersection(var("B"), var("C"))))    # (u,v)∈A×(B∩C)
    rhs = _couple_in(E.intersection(E.produit(var("A"), var("B")),
                                    E.produit(var("A"), var("C"))))               # (u,v)∈(A×B)∩(A×C)
    assert t.conclusion == equiv(lhs, rhs)
    assert lhs != rhs


def test_intersection_produits_clos_et_fidele():
    t = M.couple_dans_intersection_produits()
    assert t.est_clos and not t.hypotheses
    lhs = _couple_in(E.intersection(E.produit(var("A"), var("B")),
                                    E.produit(var("C"), var("D"))))               # (u,v)∈(A×B)∩(C×D)
    rhs = _couple_in(E.produit(E.intersection(var("A"), var("C")),
                               E.intersection(var("B"), var("D"))))               # (u,v)∈(A∩C)×(B∩D)
    assert t.conclusion == equiv(lhs, rhs)
    assert lhs != rhs


def test_parametrable():
    t = M.couple_dans_produit_distributif_reunion(u="x", v="y", a="P", b="Q", c="R")
    assert t.est_clos
    lhs = appartient(E.couple(var("x"), var("y")),
                     E.produit(var("P"), E.reunion(var("Q"), var("R"))))
    rhs = appartient(E.couple(var("x"), var("y")),
                     E.reunion(E.produit(var("P"), var("Q")), E.produit(var("P"), var("R"))))
    assert t.conclusion == equiv(lhs, rhs)


def test_theorie_inchangee_22():
    M.couple_dans_produit_distributif_reunion()
    M.couple_dans_produit_distributif_intersection()
    assert len(E.theorie_ensembles().axiomes) == 22
