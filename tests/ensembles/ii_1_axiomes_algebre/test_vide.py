"""Test V9 — caractérisation de l'ensemble vide A=∅ ⇔ (∀z)¬(z∈A)."""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, non, impl, appartient, pourtout, equiv, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import VIDE
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import (
    vide_ssi_sans_element, vide_inclus_partout, sous_ensemble_vide_ssi_egal,
    vacuite_sur_vide)


def test_vide_ssi_sans_element():
    vA, vz = var("A"), var("z")
    t = vide_ssi_sans_element("A")
    cible = equiv(egal(vA, VIDE), pourtout("z", non(appartient(vz, vA))))
    assert t.conclusion == cible and t.est_clos


# ── E II.6 §7 : ∅⊂X ───────────────────────────────────────────────────────────
def test_vide_inclus_partout():
    vX, vz = var("X"), var("z")
    t = vide_inclus_partout("X")
    # cible reconstruite depuis primitives BRUTES : (∀z)(z∈∅ ⇒ z∈X)
    cible = pourtout("z", impl(appartient(vz, VIDE), appartient(vz, vX)))
    assert t.conclusion == cible == inclus(VIDE, vX)   # == ∅⊂X
    assert t.est_clos and t.hypotheses == frozenset()
    assert len(E.theorie_ensembles().axiomes) == 22


# ── E II.6 §7 : X⊂∅ ⇔ X=∅ ─────────────────────────────────────────────────────
def test_sous_ensemble_vide_ssi_egal():
    vX = var("X")
    t = sous_ensemble_vide_ssi_egal("X")
    cible = equiv(inclus(vX, VIDE), egal(vX, VIDE))
    assert t.conclusion == cible
    assert t.est_clos and t.hypotheses == frozenset()
    assert len(E.theorie_ensembles().axiomes) == 22
    assert inclus(vX, VIDE) != egal(vX, VIDE)          # non-tautologie


# ── E II.6 §7 : (∀x)(x∈∅ ⇒ R{x}) (ex falso sur ∅) ─────────────────────────────
def test_vacuite_sur_vide():
    R = lambda u: appartient(u, var("Y"))              # relation-test R{x} := x∈Y
    vx = var("x")
    t = vacuite_sur_vide(R, "x")
    cible = pourtout("x", impl(appartient(vx, VIDE), R(vx)))   # (∀x)(x∈∅ ⇒ x∈Y)
    assert t.conclusion == cible
    assert t.est_clos and t.hypotheses == frozenset()
    assert len(E.theorie_ensembles().axiomes) == 22
