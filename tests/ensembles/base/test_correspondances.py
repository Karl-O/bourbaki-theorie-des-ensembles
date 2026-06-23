"""Tests V9 — §II.3 Correspondances : graphe, domaine/image, image directe, coupe."""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, impl, equiv, appartient, existe, pourtout, non, inclus as inclus_
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import (est_un_graphe, dom, img, image, couple, singleton,
                              VIDE, est_un_couple)
from bourbaki.ensembles.ii_3_correspondances.ensembles_correspondances import (image_croissante, image_dans_img, image_vide,
                                       coupe_membre)


def test_est_un_graphe():
    g, z = var("G"), var("z")
    assert est_un_graphe(g) == pourtout("z", impl(appartient(z, g), est_un_couple(z)))


def test_image_croissante():
    vG, vX, vY = var("G"), var("X"), var("Y")
    t = image_croissante("G", "X", "Y")
    assert t.conclusion == impl(inclus_(vX, vY), inclus_(image(vG, vX), image(vG, vY)))
    assert t.est_clos


def test_image_dans_img():
    vG, vX = var("G"), var("X")
    t = image_dans_img("G", "X")
    assert t.conclusion == inclus_(image(vG, vX), img(vG)) and t.est_clos


def test_image_vide():
    vG = var("G")
    t = image_vide("G")
    assert t.conclusion == egal(image(vG, VIDE), VIDE) and t.est_clos


def test_coupe_membre():
    vG, va, vy = var("G"), var("a"), var("y")
    t = coupe_membre("G", "a")
    cible = equiv(appartient(vy, image(vG, singleton(va))), appartient(couple(va, vy), vG))
    assert t.conclusion == cible and t.est_clos
