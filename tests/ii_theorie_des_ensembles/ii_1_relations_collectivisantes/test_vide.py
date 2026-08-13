"""Test V9 — caractérisation de l'ensemble vide A=∅ ⇔ (∀z)¬(z∈A)."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, non, impl, appartient, pourtout, equiv, inclus
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import VIDE
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_vide import (
    vide_ssi_sans_element, vide_inclus_partout, sous_ensemble_vide_ssi_egal,
    vacuite_sur_vide, vide_relation_fonctionnelle)


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


# ── E II.6 §7, Théorème 1 : (∀x)(x∉X) est fonctionnelle (univoque) en X ───────
def test_vide_relation_fonctionnelle():
    t = vide_relation_fonctionnelle()
    # cible reconstruite depuis primitives BRUTES : l'univocité en X
    #   (∀Y)(∀Z)( ((∀x)(x∉Y) et (∀x)(x∉Z)) ⇒ Y=Z )
    def sans(V):
        return pourtout("x", non(appartient(var("x"), var(V))))
    cible = pourtout("Y", pourtout("Z", impl(
        et(sans("Y"), sans("Z")), egal(var("Y"), var("Z")))))
    assert t.conclusion == cible
    assert t.est_clos and t.hypotheses == frozenset()   # CLOS : univocité pure
    assert len(E.theorie_ensembles().axiomes) == 22
    # non-tautologie : l'antécédent n'est pas le conséquent
    assert et(sans("Y"), sans("Z")) != egal(var("Y"), var("Z"))
