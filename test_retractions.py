"""Tests §II.3.8 — Rétractions et sections (Déf. 11, Prop. 8).

Chaque théorème est vérifié sur sa CONCLUSION EXACTE (== cible) et sur .est_clos.
Les cibles sont construites indépendamment (par les définitions de ensembles_abrege
ou par le mécanisme de substitution canonique), pas extraites de la preuve.
"""
from bourbaki.logique.formule import var, egal, et, appartient, impl, pourtout, existe
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.fonctions import ensembles_retractions as RS


# ── Définition 11 : prédicats bien formés ─────────────────────────────────────
def test_def11_retraction_bien_formee():
    vR, vF, vA, vx = var("R"), var("F"), var("A"), var("x")
    f = E.est_retraction(vR, vF, vA)
    attendu = pourtout("x", impl(appartient(vx, vA),
                                 egal(E.valeur(vR, E.valeur(vF, vx)), vx)))
    assert f == attendu


def test_def11_section_bien_formee():
    vS, vF, vB, vy = var("S"), var("F"), var("B"), var("y")
    f = E.est_section(vS, vF, vB)
    attendu = pourtout("y", impl(appartient(vy, vB),
                                 egal(E.valeur(vF, E.valeur(vS, vy)), vy)))
    assert f == attendu


def test_def11_synonymes_inverses():
    vR, vS, vF, vA, vB = var("R"), var("S"), var("F"), var("A"), var("B")
    assert E.est_inverse_gauche(vR, vF, vA) == E.est_retraction(vR, vF, vA)
    assert E.est_inverse_droite(vS, vF, vB) == E.est_section(vS, vF, vB)


# ── Proposition 8, sens direct (cas injectif) ─────────────────────────────────
def test_prop8_retraction_implique_injective():
    th = RS.retraction_implique_injective()
    assert th.est_clos
    assert th.conclusion == RS.cible_retraction_implique_injective()


def test_prop8_retraction_implique_injective_autres_lettres():
    th = RS.retraction_implique_injective("R0", "g", "E")
    assert th.est_clos
    assert th.conclusion == RS.cible_retraction_implique_injective("R0", "g", "E")


# ── Proposition 8, sens réciproque (construction de la section par τ) ──────────
def test_prop8_section_construite_par_tau():
    th = RS.section_construite_par_tau()
    assert th.est_clos
    assert th.conclusion == RS.cible_section_construite_par_tau()


def test_prop8_section_construite_autres_lettres():
    th = RS.section_construite_par_tau("g", "E")
    assert th.est_clos
    assert th.conclusion == RS.cible_section_construite_par_tau("g", "E")
