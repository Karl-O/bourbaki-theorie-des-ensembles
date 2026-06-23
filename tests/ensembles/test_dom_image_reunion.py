"""Tests — GAP A : corollaires dom/image set-equality d'une réunion de graphes."""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.formule import egal, var
from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_dom_image_reunion import (
    dom_reunion_graphes, image_reunion_graphes,
    dom_reunion_egale_cible, dom_reunion_egale_cible_enonce,
    image_reunion_egale_cible, image_reunion_egale_cible_enonce,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_dom_reunion_graphes_general_clos():
    # lemme général set-equality déjà présent
    thm = dom_reunion_graphes("G", "H")
    vG, vH = var("G"), var("H")
    assert thm.conclusion == egal(E.dom(E.reunion(vG, vH)),
                                  E.reunion(E.dom(vG), E.dom(vH)))


def test_dom_reunion_egale_cible():
    thm = dom_reunion_egale_cible()
    assert thm.conclusion == dom_reunion_egale_cible_enonce()
    assert thm.conclusion not in thm.hypotheses
    vG, vH = var("G"), var("H")
    vDG, vDH, vW = var("DG"), var("DH"), var("W")
    # exactement les 3 hyps structurelles
    assert egal(E.dom(vG), vDG) in thm.hypotheses
    assert egal(E.dom(vH), vDH) in thm.hypotheses
    assert egal(E.reunion(vDG, vDH), vW) in thm.hypotheses
    assert len(thm.hypotheses) == 3


def test_image_reunion_egale_cible():
    thm = image_reunion_egale_cible()
    assert thm.conclusion == image_reunion_egale_cible_enonce()
    assert thm.conclusion not in thm.hypotheses
    vG, vH = var("G"), var("H")
    vIG, vIH, vT = var("IG"), var("IH"), var("T")
    assert egal(E.image(vG, E.dom(vG)), vIG) in thm.hypotheses
    assert egal(E.image(vH, E.dom(vH)), vIH) in thm.hypotheses
    assert egal(E.reunion(vIG, vIH), vT) in thm.hypotheses
    assert len(thm.hypotheses) == 3
