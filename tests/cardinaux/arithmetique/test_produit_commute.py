"""Tests V9 — §II.2/§III.3 vers Eq(X×Y, Y×X) : briques CERTIFIÉES du graphe d'échange.

Lemmes solides issus du chantier commutativité du produit (le théorème Eq complet
reste EN COURS : injectivité à uniformiser en liants, surjectivité non commencée —
cf. docstring de ensembles_produit_commute). On certifie ici les 6 lemmes clos /
hypothétiques réellement prouvés par le noyau."""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent
from bourbaki.cardinaux.arithmetique.ensembles_produit_commute import (
    membre_produit_pr1, membre_produit_pr2, membre_produit_egal_couple,
    swap_graphe_fonctionnel, swap_graphe_domaine, swap_graphe_valeur,
    swap_graphe_injective, swap_graphe_image, swap_est_bijection,
    eq_produit_commute, _swap_graphe, _swap)


def _S(x="X", y="Y"):
    return _swap_graphe(x, y)


def test_membre_produit_pr1():
    z, vX, vY = var("z"), var("X"), var("Y")
    t = membre_produit_pr1()
    assert t.conclusion == appartient(E.pr1(z), vX)
    assert appartient(z, E.produit(vX, vY)) in t.hypotheses


def test_membre_produit_pr2():
    z, vX, vY = var("z"), var("X"), var("Y")
    t = membre_produit_pr2()
    assert t.conclusion == appartient(E.pr2(z), vY)
    assert appartient(z, E.produit(vX, vY)) in t.hypotheses


def test_membre_produit_egal_couple():
    z, vX, vY = var("z"), var("X"), var("Y")
    t = membre_produit_egal_couple()
    # z = (pr₁z, pr₂z) : un élément du produit se reconstruit de ses projections
    assert t.conclusion == egal(z, E.couple(E.pr1(z), E.pr2(z)))
    assert appartient(z, E.produit(vX, vY)) in t.hypotheses


def test_swap_graphe_fonctionnel():
    t = swap_graphe_fonctionnel()
    # S = graphe d'échange est fonctionnel (forme est_fonctionnel sur S)
    assert t.conclusion == E.est_fonctionnel(_S()) and t.est_clos


def test_swap_graphe_domaine():
    vX, vY = var("X"), var("Y")
    t = swap_graphe_domaine()
    assert t.conclusion == egal(E.dom(_S()), E.produit(vX, vY)) and t.est_clos


def test_swap_graphe_valeur():
    u, vX, vY = var("u"), var("X"), var("Y")
    t = swap_graphe_valeur()
    # S(u) = (pr₂u, pr₁u) avec les liants a,b du terme d'échange
    swap_val = E.couple(E.pr2(u, "a", "b"), E.pr1(u, "a", "b"))
    assert t.conclusion == egal(E.valeur(_S(), u), swap_val)
    assert appartient(u, E.produit(vX, vY)) in t.hypotheses


def test_swap_graphe_injective():
    vX, vY = var("X"), var("Y")
    t = swap_graphe_injective()
    # S = graphe d'échange est injectif sur X×Y (fix du désaccord de liants a,b)
    assert t.conclusion == E.injective_dans(_S(), E.produit(vX, vY)) and t.est_clos


def test_swap_graphe_image():
    vX, vY = var("X"), var("Y")
    t = swap_graphe_image()
    # image(S, X×Y) = Y×X  (surjectivité : tout (c,d)∈Y×X est S((d,c)))
    assert t.conclusion == egal(E.image(_S(), E.produit(vX, vY)),
                                E.produit(vY, vX)) and t.est_clos


def test_swap_est_bijection():
    vX, vY = var("X"), var("Y")
    t = swap_est_bijection()
    # est_bijection_de(S, X×Y, Y×X) : les 4 conjoints (func, dom, inj, image)
    assert t.conclusion == est_bijection_de(_S(), E.produit(vX, vY),
                                            E.produit(vY, vX)) and t.est_clos


def test_eq_produit_commute():
    vX, vY = var("X"), var("Y")
    t = eq_produit_commute()
    # Eq(X×Y, Y×X) : commutativité du produit à équipotence près (§III.3)
    assert t.conclusion == equipotent(E.produit(vX, vY),
                                      E.produit(vY, vX)) and t.est_clos
