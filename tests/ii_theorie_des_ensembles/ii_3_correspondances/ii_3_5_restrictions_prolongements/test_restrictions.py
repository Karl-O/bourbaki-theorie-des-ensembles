"""Tests §II.3.5 — Restrictions et prolongements de fonctions.

Chaque théorème : conclusion EXACTE (== cible) et clôture (.est_clos).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, appartient, existe, inclus, impl, pourtout,
                     equiv)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_5_restrictions_prolongements import ensembles_restrictions as R


def test_couple_restriction():
    vF, vX, vu, vv = var("F"), var("X"), var("u"), var("v")
    t = R.couple_restriction()
    cible = equiv(appartient(E.couple(vu, vv), E.restriction(vF, vX)),
                  et(appartient(vu, vX), appartient(E.couple(vu, vv), vF)))
    assert t.conclusion == cible
    assert t.est_clos


def test_restriction_incluse():
    vF, vX = var("F"), var("X")
    t = R.restriction_incluse()
    assert t.conclusion == inclus(E.restriction(vF, vX), vF)
    assert t.est_clos


def test_prolongement_reflexif():
    vF = var("F")
    t = R.prolongement_reflexif()
    assert t.conclusion == inclus(vF, vF)
    assert t.est_clos


def test_prolongement_transitif():
    vF, vG, vH = var("F"), var("G"), var("H")
    t = R.prolongement_transitif()
    cible = impl(et(inclus(vF, vG), inclus(vG, vH)), inclus(vF, vH))
    assert t.conclusion == cible
    assert t.est_clos


def test_coincidence_meme_graphe():
    vF, vG, vx = var("F"), var("G"), var("x")
    t = R.coincidence_meme_graphe()
    cible = impl(egal(vF, vG),
                 pourtout("x", impl(appartient(vx, E.dom(vF)),
                                    egal(E.valeur(vF, vx), E.valeur(vG, vx)))))
    assert t.conclusion == cible
    assert t.est_clos


def test_axiome_restriction_dans_theorie():
    th = E.theorie_ensembles()
    assert any(ax == E.AXIOME_RESTRICTION for ax in th.axiomes)
