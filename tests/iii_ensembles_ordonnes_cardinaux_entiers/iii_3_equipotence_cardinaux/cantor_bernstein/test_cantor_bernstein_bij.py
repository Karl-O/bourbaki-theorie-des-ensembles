"""Tests — CANTOR–BERNSTEIN, assemblage : briques restriction + morceau f|D.

Vérifie la CONCLUSION EXACTE et les HYPOTHÈSES de chaque théorème via le noyau.
Les briques de restriction (image/dom/valeur/injective) sont GÉNÉRALES ; morceau_fD
assemble le premier morceau de la bijection (f|D : D → f⟨D⟩).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, impl, inclus, appartient
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein import ensembles_cantor_bernstein as CB
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein import ensembles_cantor_bernstein_bij as B
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_injection_de, est_bijection_de


def test_restriction_image_egale_image():
    """⊢ image(f|X, X) = image(f, X), clos."""
    th = B.restriction_image_egale_image()
    vF, vX = var("F"), var("X")
    fX = E.restriction(vF, vX)
    assert th.est_clos
    assert th.conclusion == egal(E.image(fX, vX), E.image(vF, vX))


def test_restriction_dom_sous_inclusion():
    """⊢ (X⊂dom F) ⇒ (dom(f|X)=X), clos."""
    th = B.restriction_dom_sous_inclusion()
    vF, vX = var("F"), var("X")
    fX = E.restriction(vF, vX)
    assert th.est_clos
    assert th.conclusion == impl(inclus(vX, E.dom(vF)), egal(E.dom(fX), vX))


def test_restriction_valeur():
    """{F fonct, u∈X, u∈dom F} ⊢ (f|X)(u)=F(u)."""
    th = B.restriction_valeur()
    vF, vX, vu = var("F"), var("X"), var("u")
    fX = E.restriction(vF, vX)
    assert th.conclusion == egal(E.valeur(fX, vu), E.valeur(vF, vu))
    assert th.hypotheses == frozenset({
        E.est_fonctionnel(vF), appartient(vu, vX), appartient(vu, E.dom(vF))})


def test_restriction_injective():
    """{F fonct, injective_dans(F,X), X⊂dom F} ⊢ injective_dans(f|X, X)."""
    th = B.restriction_injective()
    vF, vX = var("F"), var("X")
    fX = E.restriction(vF, vX)
    assert th.conclusion == E.injective_dans(fX, vX)
    assert th.hypotheses == frozenset({
        E.est_fonctionnel(vF), E.injective_dans(vF, vX), inclus(vX, E.dom(vF))})


def test_morceau_fD():
    """{est_injection_de(f,a,b)} ⊢ est_bijection_de(f|D, D, f⟨D⟩), clos.

    PREMIER MORCEAU de la bijection de Cantor–Bernstein : sur le point fixe D, f
    est une bijection de D sur f⟨D⟩."""
    th = B.morceau_fD()
    vA, vB, vf, vg = var("A"), var("B"), var("f"), var("g")
    dterm = CB.D(vA, vB, vf, vg)
    fD = E.restriction(vf, dterm)
    fImgD = E.image(vf, dterm)
    assert th.est_clos
    assert th.conclusion == impl(est_injection_de(vf, vA, vB),
                                 est_bijection_de(fD, dterm, fImgD))
