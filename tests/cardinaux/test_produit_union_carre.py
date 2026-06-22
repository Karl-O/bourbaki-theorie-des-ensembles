"""TASK A — distribution ensembliste pleine produit/réunion + (A∪B)²."""
from bourbaki.logique.formule import var, egal
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_produit_union_carre import (
    existe_ou, produit_union_gauche, produit_union_droite,
    produit_union_carre, carre_reunion_S0_U,
)


def _A():
    return var("A"), var("B")


def test_existe_ou_clos():
    from bourbaki.logique.formule import appartient
    r = existe_ou("w", appartient(var("p"), var("A")), appartient(var("p"), var("B")))
    assert not r.hypotheses


def test_produit_union_gauche_clos():
    vA, vB = _A()
    vC = var("C")
    r = produit_union_gauche()
    assert not r.hypotheses
    tu = E.produit(E.reunion(vA, vB), vC)
    tv = E.reunion(E.produit(vA, vC), E.produit(vB, vC))
    assert r.conclusion == egal(tu, tv)


def test_produit_union_droite_clos():
    vA, vB = _A()
    vC = var("C")
    r = produit_union_droite()
    assert not r.hypotheses
    tu = E.produit(vA, E.reunion(vB, vC))
    tv = E.reunion(E.produit(vA, vB), E.produit(vA, vC))
    assert r.conclusion == egal(tu, tv)


def test_produit_union_carre_clos():
    vA, vB = _A()
    AB = E.reunion(vA, vB)
    AA, AxB, BxA, BB = (E.produit(vA, vA), E.produit(vA, vB),
                        E.produit(vB, vA), E.produit(vB, vB))
    r = produit_union_carre()
    assert not r.hypotheses
    cible = egal(E.produit(AB, AB),
                 E.reunion(AA, E.reunion(AxB, E.reunion(BxA, BB))))
    assert r.conclusion == cible


def test_carre_reunion_S0_U_clos():
    r = carre_reunion_S0_U()
    assert not r.hypotheses


def test_theorie_22():
    assert len(list(E.theorie_ensembles().axiomes)) == 22
