"""Test V9 — caractérisation de l'ensemble vide A=∅ ⇔ (∀z)¬(z∈A)."""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, non, appartient, pourtout, equiv
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import VIDE
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import vide_ssi_sans_element


def test_vide_ssi_sans_element():
    vA, vz = var("A"), var("z")
    t = vide_ssi_sans_element("A")
    cible = equiv(egal(vA, VIDE), pourtout("z", non(appartient(vz, vA))))
    assert t.conclusion == cible and t.est_clos
