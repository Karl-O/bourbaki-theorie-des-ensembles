"""Tests §IV.2 (suite) — Structures FINALES (dual des initiales).

Fidélité des définitions (FI), image directe, structure quotient ; certification du
théorème logique direct (sens facile de (FI)).
"""
from bourbaki.logique.formule import (var, et, impl, equiv, pourtout, appartient,
                                       app, alpha_egal)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.structures.iv_2_morphismes_structures_derivees import ensembles_universel_finale as Fi
from bourbaki.structures.iv_2_morphismes_structures_derivees import ensembles_universel_morphismes as M


def _fam():
    return (lambda t: app("A", t), lambda t: app("Sig", t), lambda t: app("g", t))


def test_propriete_FI_forme():
    mor = M._morph_defaut()
    af, sf, gf = _fam()
    fi = Fi.propriete_FI("E", var("Fstruct"), var("I0"), af, sf, gf, morph=mor)
    assert fi.tag == "non"          # (∀E')(∀𝒮')(∀f)(equiv …)
    assert "composee" in repr(fi)   # f ∘ g_ι


def test_est_structure_finale_est_FI():
    mor = M._morph_defaut()
    af, sf, gf = _fam()
    a = Fi.est_structure_finale("E", var("Fstruct"), var("I0"), af, sf, gf, mor)
    b = Fi.propriete_FI("E", var("Fstruct"), var("I0"), af, sf, gf, morph=mor)
    assert alpha_egal(a, b)


def test_finale_implique_g_iota_morphisme_certifie():
    """{(FI), id morphisme} ⊢ (∀ι)(ι∈I ⇒ Δ_E∘g_ι morphisme)."""
    t = Fi.finale_implique_g_iota_morphisme()
    assert t.hypotheses             # non clos (axiomes FI + MO_III)
    assert t.conclusion.tag == "non"   # ∀ι


def test_image_directe_caracterisation():
    mor = M._morph_defaut()
    car = Fi.image_directe_structure(var("A"), var("S"), var("f"), var("E"),
                                     morph=mor)
    assert car.tag == "non"   # (∀E')(∀𝒮')(∀h)(equiv …)


def test_structure_quotient_via_image_directe():
    """structure quotient de 𝒮 par R = image directe par l'application canonique."""
    mor = M._morph_defaut()
    car = Fi.structure_quotient(var("A"), var("S"), var("R"), morph=mor)
    e = E.quotient(var("R"), var("A"))                 # A/R
    phi = E.application_canonique(var("R"), var("A"))  # appli canonique A → A/R
    cible = Fi.image_directe_structure(var("A"), var("S"), phi, e, morph=mor)
    assert alpha_egal(car, cible)
