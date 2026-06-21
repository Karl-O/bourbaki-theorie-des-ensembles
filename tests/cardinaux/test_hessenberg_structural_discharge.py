"""Tests — décharge structurelle des hyps honnêtes de Hessenberg a²=a (cat. A, C, E)."""
from bourbaki.logique.formule import (
    var, egal, et, non, impl, pourtout, appartient, inclus, equiv,
)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_bijection_de, inf_egal_card,
)
import bourbaki.cardinaux.ensembles_hessenberg_structural_discharge as M


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_bijection_dom():
    t = M.bijection_dom()
    vF, vX, vY = var("phi"), var("X"), var("Y")
    assert t.conclusion == egal(E.dom(vF), vX)
    assert set(t.hypotheses) == {est_bijection_de(vF, vX, vY)}
    assert t.conclusion not in t.hypotheses


def test_bijection_image():
    t = M.bijection_image()
    vF, vX, vY = var("phi"), var("X"), var("Y")
    assert t.conclusion == egal(E.image(vF, vX), vY)
    assert set(t.hypotheses) == {est_bijection_de(vF, vX, vY)}
    assert t.conclusion not in t.hypotheses


def test_frame_dom_image():
    t = M.frame_dom_image()
    vS, vphi = var("S0"), var("phi0")
    SxS = E.produit(vS, vS)
    assert t.conclusion == et(egal(E.dom(vphi), SxS), egal(E.image(vphi, SxS), vS))
    assert set(t.hypotheses) == {est_bijection_de(vphi, SxS, vS)}


def test_U_non_vide():
    t = M.U_non_vide()
    vU = var("Ucadre")
    assert t.conclusion == non(egal(vU, E.VIDE))
    assert set(t.hypotheses) == {non(egal(cardinal(vU), cardinal(E.VIDE)))}
    assert t.conclusion not in t.hypotheses


def test_U_disjoint_S0():
    t = M.U_disjoint_S0()
    vE, vS, vU = var("E"), var("S0"), var("Ucadre")
    vz = var("z")
    assert t.conclusion == pourtout("z", impl(appartient(vz, vU), non(appartient(vz, vS))))
    assert set(t.hypotheses) == {inclus(vU, E.difference(vE, vS))}
    assert t.conclusion not in t.hypotheses


def test_card_inclus_inf_egal():
    t = M.card_inclus_inf_egal()
    vE, vS = var("E"), var("S0")
    assert t.conclusion == inf_egal_card(cardinal(vS), cardinal(vE))
    assert set(t.hypotheses) == {inclus(vS, vE)}
    assert t.conclusion not in t.hypotheses


def test_couple_dans_produit_reunion_gauche():
    t = M.couple_dans_produit_reunion_gauche()
    assert t.est_clos
    vu, vv, vA, vB, vC = var("u"), var("v"), var("A"), var("B"), var("C")
    AB = E.reunion(vA, vB)
    cpl = E.couple(vu, vv)
    lhs = appartient(cpl, E.produit(AB, vC))
    rhs = appartient(cpl, E.reunion(E.produit(vA, vC), E.produit(vB, vC)))
    assert t.conclusion == equiv(lhs, rhs)
