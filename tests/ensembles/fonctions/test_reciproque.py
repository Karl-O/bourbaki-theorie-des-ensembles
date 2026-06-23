"""Test V9 — §II.3.2 graphe réciproque : (x,y)∈G⁻¹ ⇔ (y,x)∈G ;
projections du réciproque (pr₁G⁻¹=pr₂G, pr₂G⁻¹=pr₁G) ; (X×Y)⁻¹=Y×X."""
from __future__ import annotations

from bourbaki.logique.formule import var, equiv, egal, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import couple, reciproque, dom, img, produit
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import (couple_reciproque, pr1_reciproque,
                                  pr2_reciproque, reciproque_produit)


def test_couple_reciproque():
    vG, vu, vv = var("G"), var("u"), var("v")
    t = couple_reciproque("G", "u", "v")
    cible = equiv(appartient(couple(vu, vv), reciproque(vG)),
                  appartient(couple(vv, vu), vG))
    assert t.conclusion == cible and t.est_clos


def test_pr1_reciproque():
    vG = var("G")
    t = pr1_reciproque("G")
    assert t.conclusion == egal(dom(reciproque(vG)), img(vG)) and t.est_clos


def test_pr2_reciproque():
    vG = var("G")
    t = pr2_reciproque("G")
    assert t.conclusion == egal(img(reciproque(vG)), dom(vG)) and t.est_clos


def test_reciproque_produit():
    vX, vY = var("X"), var("Y")
    t = reciproque_produit("X", "Y")
    assert t.conclusion == egal(reciproque(produit(vX, vY)), produit(vY, vX)) and t.est_clos
