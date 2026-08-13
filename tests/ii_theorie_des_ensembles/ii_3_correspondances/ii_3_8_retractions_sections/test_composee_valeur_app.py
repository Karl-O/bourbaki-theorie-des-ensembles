# -*- coding: utf-8 -*-
"""Test brique Groupe B — composée-valeur niveau APPLICATION (généralisable)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_8_retractions_sections.ensembles_composee_valeurs import (
    composee_valeur_app, enonce_composee_valeur_app,
    injective_facteur_droit, enonce_injective_facteur_droit,
    surjective_facteur_gauche, enonce_surjective_facteur_gauche,
    image_incluse_arrivee)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import est_application


_HYPS_APP = frozenset([
    est_application(E.var("F"), E.var("E"), E.var("Fp")),
    est_application(E.var("G"), E.var("Fp"), E.var("Gp"))])


def test_composee_valeur_app():
    """⊢ {est_application(F,E,Fp), est_application(G,Fp,Gp)} (u∈E)⇒((g∘f)(u)=g(f(u)))."""
    r = composee_valeur_app()
    assert r.conclusion == enonce_composee_valeur_app()
    assert r.hypotheses == _HYPS_APP


def test_injective_facteur_droit():
    """⊢ {est_application ×2} injective_dans(G∘F,E) ⇒ injective_dans(F,E)."""
    r = injective_facteur_droit()
    assert r.conclusion == enonce_injective_facteur_droit()
    assert r.hypotheses == _HYPS_APP


def test_image_incluse_arrivee():
    """⊢ {est_application(F,E,B)} f⟨E⟩ ⊂ B."""
    r = image_incluse_arrivee()
    assert r.conclusion == E.inclus(E.image(E.var("F"), E.var("E")), E.var("B"))
    assert r.hypotheses == frozenset([est_application(E.var("F"), E.var("E"), E.var("B"))])


def test_surjective_facteur_gauche():
    """⊢ {est_application ×2} est_surjective(F∘G,Fs,Fs) ⇒ est_surjective(F,E,Fs)."""
    r = surjective_facteur_gauche()
    assert r.conclusion == enonce_surjective_facteur_gauche()
    assert r.hypotheses == frozenset([
        est_application(E.var("F"), E.var("E"), E.var("Fs")),
        est_application(E.var("G"), E.var("Fs"), E.var("E"))])


def test_theorie_inchangee():
    composee_valeur_app()
    injective_facteur_droit()
    surjective_facteur_gauche()
    image_incluse_arrivee()
    assert len(E.theorie_ensembles().axiomes) == 22
