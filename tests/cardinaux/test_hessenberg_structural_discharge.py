"""Tests — décharge structurelle des hyps honnêtes de Hessenberg a²=a (cat. A, C, E)."""
from bourbaki.logique.formule import (
    var, egal, et, non, impl, pourtout, appartient, inclus,
)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, est_bijection_de,
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
