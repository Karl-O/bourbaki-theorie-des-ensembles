"""Test V9 — §II.3.3 graphe composé : (x,z)∈G'∘G ⇔ (∃y)((x,y)∈G et (y,z)∈G')."""
from __future__ import annotations

from formule import var, equiv, egal, et, appartient, existe
from ensembles_abrege import couple, composee, image
from ensembles_composee import couple_composee, image_composee


def test_couple_composee():
    vGp, vG, vx, vz, vy = var("Gp"), var("G"), var("x"), var("z"), var("y")
    t = couple_composee("Gp", "G", "x", "z")
    rhs = existe("y", et(appartient(couple(vx, vy), vG), appartient(couple(vy, vz), vGp)))
    cible = equiv(appartient(couple(vx, vz), composee(vGp, vG)), rhs)
    assert t.conclusion == cible and t.est_clos


def test_image_composee():
    vGp, vG, vA = var("Gp"), var("G"), var("A")
    t = image_composee("Gp", "G", "A")
    cible = egal(image(composee(vGp, vG), vA), image(vGp, image(vG, vA)))
    assert t.conclusion == cible and t.est_clos
