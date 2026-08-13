"""Tests §III.2 — LEMME 4 (forme E=F) : une application strictement croissante d'un
ensemble bien ordonné dans lui-même ne décroît jamais  (x∈E ⇒ R{x,f(x)}).

On certifie : l'axiome définitionnel de A (theorie=22), A=∅ sous les bonnes hypothèses,
et Lemme 4 lui-même à 3 hypothèses STRUCTURELLES (bon ordre canonique + f:E→E + f
strictement croissante), conclusion fidèle, non tautologique.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments import ensembles_lemme4_croissante as L
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import est_strictement_croissante


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


def test_cor1_pas_dans_segment():
    """{ bo, a∈E, g strict crois. E→E } ⊢ ¬(∀t)(t∈E ⇒ g(t)∈]←,a[)  (Cor 1 §III.2)."""
    c1 = L.cor1_pas_dans_segment()
    assert not c1.est_clos
    assert len(c1.hypotheses) == 3
    assert c1.conclusion == L.cor1_pas_dans_segment_cible()
    assert c1.conclusion not in c1.hypotheses
    # le bon ordre CANONIQUE est bien l'hypothèse (chainable)
    Rf = L._R_de("R")
    assert E.est_bien_ordonne(Rf, var("E")) in c1.hypotheses


def test_parametrable():
    l4 = L.lemme_4("Rp", "F", "g")
    assert len(l4.hypotheses) == 3
    assert l4.conclusion == L.lemme_4_cible("Rp", "F", "g")


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
