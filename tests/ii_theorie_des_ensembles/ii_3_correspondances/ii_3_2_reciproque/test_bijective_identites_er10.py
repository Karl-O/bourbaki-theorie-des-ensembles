# -*- coding: utf-8 -*-
"""Test n°77 (E.R.10 item 10d) — assemblage f bijective ⇔ identités image/préimage.

Étape 1 : pont H_app depuis est_application."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import est_application
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_bijective_identites_er10 import (
    hyp_applicative_de_application, hyp_applicative,
    inj_dans_implique_graphe_injectif, inj_dans_implique_reciproque_fonctionnel,
    direction_bijective_vers_identites, enonce_direction_bijective_vers_identites,
    converse_Y_vers_surjective, enonce_converse_Y_vers_surjective,
    converse_X_vers_injective, enonce_converse_X_vers_injective,
    bijective_ssi_identites, enonce_bijective_ssi_identites)


def test_hyp_applicative_de_application():
    """⊢ {est_application(f,E,F), X⊂E} (∀x)(x∈X ⇒ (x,f(x))∈f)."""
    r = hyp_applicative_de_application()
    assert r.conclusion == hyp_applicative(E.var("f"), E.var("X"))
    assert r.hypotheses == frozenset([
        est_application(E.var("f"), E.var("E"), E.var("F")),
        inclus(E.var("X"), E.var("E"))])


def test_inj_dans_implique_reciproque_fonctionnel():
    """⊢ {est_application(f,E,F)} injective_dans(f,E) ⇒ est_fonctionnel(f⁻¹)."""
    r = inj_dans_implique_reciproque_fonctionnel()
    assert r.conclusion == impl(E.injective_dans(E.var("f"), E.var("E")),
                                E.est_fonctionnel(E.reciproque(E.var("f"))))
    assert r.hypotheses == frozenset([
        est_application(E.var("f"), E.var("E"), E.var("F"))])


def test_direction_bijective_vers_identites():
    """⊢ {est_application(f,E,F)} bijective ⇒ (∀X f⁻¹⟨f⟨X⟩⟩=X et ∀Y f⟨f⁻¹⟨Y⟩⟩=Y)."""
    r = direction_bijective_vers_identites()
    assert r.conclusion == enonce_direction_bijective_vers_identites()
    assert r.hypotheses == frozenset([
        est_application(E.var("f"), E.var("E"), E.var("F"))])


def test_converse_Y_vers_surjective():
    """⊢ {est_application(f,E,F)} (∀Y)(Y⊂F ⇒ f⟨f⁻¹⟨Y⟩⟩=Y) ⇒ est_surjective(f,E,F)."""
    r = converse_Y_vers_surjective()
    assert r.conclusion == enonce_converse_Y_vers_surjective()
    assert r.hypotheses == frozenset([
        est_application(E.var("f"), E.var("E"), E.var("F"))])


def test_converse_X_vers_injective():
    """⊢ {est_application(f,E,F)} (∀X)(X⊂E ⇒ f⁻¹⟨f⟨X⟩⟩=X) ⇒ injective_dans(f,E)."""
    r = converse_X_vers_injective()
    assert r.conclusion == enonce_converse_X_vers_injective()
    assert r.hypotheses == frozenset([
        est_application(E.var("f"), E.var("E"), E.var("F"))])


def test_bijective_ssi_identites():
    """⊢ est_application(f,E,F) ⇒ ((∀X f⁻¹⟨f⟨X⟩⟩=X et ∀Y f⟨f⁻¹⟨Y⟩⟩=Y) ⇔ bijective) — CLOS, 0 hyp."""
    r = bijective_ssi_identites()
    assert r.conclusion == enonce_bijective_ssi_identites()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_theorie_inchangee():
    bijective_ssi_identites()
    assert len(E.theorie_ensembles().axiomes) == 22
