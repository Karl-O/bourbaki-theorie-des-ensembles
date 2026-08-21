# -*- coding: utf-8 -*-
"""Tests §III.6 (prérequis Lemme 2) — 2-valuation, étage 1 : ponts commut/assoc ops."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_deux_valuation import (
    ops_produit_commutatif, ops_produit_associatif,
)


def test_ops_produit_commutatif():
    """⊢ a·b = b·a (niveau opérations)."""
    va, vb = var("acm"), var("bcm")
    r = ops_produit_commutatif(va, vb)
    assert not r.hypotheses
    assert r.conclusion == egal(produit_cardinal_binaire(va, vb),
                                produit_cardinal_binaire(vb, va))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_ops_produit_associatif():
    """⊢ (a·b)·c = a·(b·c) (niveau opérations)."""
    va, vb, vc = var("aas"), var("bas"), var("cas")
    r = ops_produit_associatif(va, vb, vc)
    assert not r.hypotheses
    assert r.conclusion == egal(
        produit_cardinal_binaire(produit_cardinal_binaire(va, vb), vc),
        produit_cardinal_binaire(va, produit_cardinal_binaire(vb, vc)))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
