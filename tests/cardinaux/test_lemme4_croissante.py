"""Tests §III.2 — LEMME 4 (forme E=F) : une application strictement croissante d'un
ensemble bien ordonné dans lui-même ne décroît jamais  (x∈E ⇒ R{x,f(x)}).

On certifie : l'axiome définitionnel de A (theorie=22), A=∅ sous les bonnes hypothèses,
et Lemme 4 lui-même à 3 hypothèses STRUCTURELLES (bon ordre canonique + f:E→E + f
strictement croissante), conclusion fidèle, non tautologique.
"""
from bourbaki.logique.formule import var, egal
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_lemme4_croissante as L
from bourbaki.ordre.ensembles_ordre_monotone import est_strictement_croissante


def test_axiome_A_membre_clos():
    """u∈A ⇔ (u∈E et f(u)<u) — axiome définitionnel instancié, CLOS."""
    am = L.A_membre()
    assert am.est_clos
    ie = L.A_inclus_E()
    assert ie.est_clos and not ie.hypotheses        # A⊂E inconditionnel


def test_A_vide():
    """{ bo, f:E→E, f strict crois. } ⊢ A = ∅."""
    av = L.A_vide()
    assert not av.est_clos
    assert len(av.hypotheses) == 3
    A = L.A_bad(var("R"), var("E"), var("f"))
    assert av.conclusion == egal(A, E.VIDE)
    assert av.conclusion not in av.hypotheses


def test_lemme_4():
    """{ bo, f:E→E, f strict crois. } ⊢ (∀x)(x∈E ⇒ R{x,f(x)})."""
    l4 = L.lemme_4()
    assert not l4.est_clos
    assert len(l4.hypotheses) == 3
    assert l4.conclusion == L.lemme_4_cible()
    assert l4.conclusion not in l4.hypotheses
    # les 3 hypothèses sont STRUCTURELLES : bon ordre canonique, f:E→E, f strict croissante
    Rf = L._R_de("R")
    bo = E.est_bien_ordonne(Rf, var("E"))
    scr = est_strictement_croissante(var("R"), var("R"), var("f"), var("E"), var("E"))
    assert bo in l4.hypotheses                       # bon ordre CANONIQUE (chainable)
    assert scr in l4.hypotheses                       # stricte croissance réellement requise


def test_parametrable():
    l4 = L.lemme_4("Rp", "F", "g")
    assert len(l4.hypotheses) == 3
    assert l4.conclusion == L.lemme_4_cible("Rp", "F", "g")


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
