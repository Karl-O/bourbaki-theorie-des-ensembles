"""Tests — PONT GÉNÉRAL valeur d'un graphe fonctionnel dans son but (§II.3.4).

Généralisation à (x, E, F) quelconques des lemmes ∅-spécialisés de a^1=a.  On vérifie
clôture conditionnelle (hypothèses exactes) et conclusions Bourbaki exactes.
"""
from bourbaki.ensembles.fonctions.ii_3_4_fonctions_valeur.ensembles_valeur_codomaine import (
    couple_valeur_dans_graphe, valeur_dans_codomaine)
from bourbaki.logique.formule import var, egal, appartient, inclus
import bourbaki.ensembles.ensembles_abrege as E


def test_couple_valeur_dans_graphe():
    th = couple_valeur_dans_graphe("G", "E", "x")
    assert not th.est_clos                              # conditionnel : 2 hypothèses
    vG, vE, vx = var("G"), var("E"), var("x")
    # conclusion = (x, G(x)) ∈ G
    assert th.conclusion == appartient(E.couple(vx, E.valeur(vG, vx)), vG)
    # hypothèses EXACTEMENT {dom G = E, x ∈ E}
    hyps = list(th.hypotheses)
    assert egal(E.dom(vG), vE) in hyps
    assert appartient(vx, vE) in hyps
    assert len(hyps) == 2


def test_valeur_dans_codomaine():
    th = valeur_dans_codomaine("G", "E", "F", "x")
    assert not th.est_clos                              # conditionnel : 3 hypothèses
    vG, vE, vF, vx = var("G"), var("E"), var("F"), var("x")
    # conclusion = G(x) ∈ F
    assert th.conclusion == appartient(E.valeur(vG, vx), vF)
    # hypothèses EXACTEMENT {G⊂E×F, dom G=E, x∈E}
    hyps = list(th.hypotheses)
    assert inclus(vG, E.produit(vE, vF)) in hyps
    assert egal(E.dom(vG), vE) in hyps
    assert appartient(vx, vE) in hyps
    assert len(hyps) == 3


def test_valeur_dans_codomaine_termes():
    # robustesse : fonctionne avec des TERMES (pas seulement des noms)
    A, B = var("A"), var("B")
    th = valeur_dans_codomaine(var("H"), A, B, var("u"))
    assert th.conclusion == appartient(E.valeur(var("H"), var("u")), B)
