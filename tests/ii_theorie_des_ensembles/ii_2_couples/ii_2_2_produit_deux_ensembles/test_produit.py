"""Tests V9 — §II.2.2 Produit X×Y : définition, monotonie (Prop 2 sens direct)."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, ou, impl, appartient, existe, egal, inclus, equiv, afficher_f
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import produit, couple, est_un_couple, pr1, pr2, VIDE
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import (produit_inclusion_facile, couple_dans_produit,
                               couple_dans_produit_ssi,
                               produit_projections, produit_vide_si,
                               produit_vide_dur, produit_vide,
                               produit_inclusion_reciproque_gauche,
                               produit_inclusion_reciproque_droite)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import non


def test_est_un_couple():
    z, x, y = var("z"), var("x"), var("y")
    assert est_un_couple(z) == existe("x", existe("y", egal(z, couple(x, y))))


def test_produit_terme():
    a, b = var("a"), var("b")
    assert produit(a, b).nom == "produit"


def test_produit_inclusion_facile():
    vA, vB, vAp, vBp = var("A"), var("B"), var("Ap"), var("Bp")
    t = produit_inclusion_facile("A", "B", "Ap", "Bp")
    cible = impl(et(inclus(vAp, vA), inclus(vBp, vB)),
                 inclus(produit(vAp, vBp), produit(vA, vB)))
    assert t.conclusion == cible and t.est_clos


def test_couple_dans_produit():
    vu, vv, vA, vB = var("u"), var("v"), var("A"), var("B")
    t = couple_dans_produit("u", "v", "A", "B")
    cible = impl(et(appartient(vu, vA), appartient(vv, vB)),
                 appartient(couple(vu, vv), produit(vA, vB)))
    assert t.conclusion == cible and t.est_clos


def test_couple_dans_produit_ssi():
    vu, vv, vA, vB = var("u"), var("v"), var("A"), var("B")
    t = couple_dans_produit_ssi("u", "v", "A", "B")
    cible = equiv(appartient(couple(vu, vv), produit(vA, vB)),
                  et(appartient(vu, vA), appartient(vv, vB)))
    assert t.conclusion == cible and t.est_clos


def test_produit_projections():
    vA, vB, vz = var("A"), var("B"), var("z")
    t = produit_projections("A", "B", "z")
    cible = impl(appartient(vz, produit(vA, vB)),
                 et(appartient(pr1(vz), vA), appartient(pr2(vz), vB)))
    assert t.conclusion == cible and t.est_clos


def test_produit_vide():
    vA, vB = var("A"), var("B")
    P = egal(produit(vA, vB), VIDE)
    Q = ou(egal(vA, VIDE), egal(vB, VIDE))
    assert produit_vide_si("A", "B").conclusion == impl(Q, P)
    assert produit_vide_dur("A", "B").conclusion == impl(P, Q)
    t = produit_vide("A", "B")
    assert t.conclusion == equiv(P, Q) and t.est_clos


def test_produit_inclusion_reciproque():
    vA, vB, vAp, vBp = var("A"), var("B"), var("Ap"), var("Bp")
    sub = inclus(produit(vAp, vBp), produit(vA, vB))
    g = produit_inclusion_reciproque_gauche()
    assert g.conclusion == impl(non(egal(vBp, VIDE)), impl(sub, inclus(vAp, vA)))
    assert g.est_clos
    d = produit_inclusion_reciproque_droite()
    assert d.conclusion == impl(non(egal(vAp, VIDE)), impl(sub, inclus(vBp, vB)))
    assert d.est_clos
