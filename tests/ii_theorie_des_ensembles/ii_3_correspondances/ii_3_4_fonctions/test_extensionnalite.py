"""Tests V9 — §II.3 Extensionnalité fonctionnelle (graphe_egal_par_valeurs)."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, appartient, existe, pourtout
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import (est_fonctionnel, est_un_graphe,
                                                 dom, valeur, couple)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    couple_dans_dom, egalite_valeurs, graphe_egal_par_valeurs)


def test_couple_dans_dom():
    vF, vx, vy = var("F"), var("x"), var("y")
    t = couple_dans_dom("F", "x", "y")
    assert t.conclusion == appartient(vx, dom(vF))
    # seule hypothèse : (x,y)∈F
    assert t.hypotheses == {appartient(couple(vx, vy), vF)}


def test_egalite_valeurs_forme():
    vF, vG, vx = var("F"), var("G"), var("x")
    f = egalite_valeurs("F", "G")
    assert f == pourtout("x", impl(appartient(vx, dom(vF)),
                                   egal(valeur(vF, vx), valeur(vG, vx))))


def test_graphe_egal_par_valeurs_conclusion():
    vF, vG = var("F"), var("G")
    t = graphe_egal_par_valeurs("F", "G")
    hyp = et(et(et(et(et(
        est_fonctionnel(vF), est_fonctionnel(vG)),
        est_un_graphe(vF)), est_un_graphe(vG)),
        egal(dom(vF), dom(vG))),
        egalite_valeurs(vF, vG))
    assert t.conclusion == impl(hyp, egal(vF, vG))


def test_graphe_egal_par_valeurs_clos():
    # Théorème CLOS (aucune hypothèse résiduelle) : l'implication est démontrée.
    t = graphe_egal_par_valeurs("F", "G")
    assert t.hypotheses == frozenset()
    assert t.est_clos


def test_graphe_egal_par_valeurs_termes():
    # Robustesse : fonctionne aussi sur des graphes nommés différemment.
    vA, vB = var("A"), var("B")
    t = graphe_egal_par_valeurs("A", "B")
    assert t.conclusion.sous[1] == egal(vA, vB)   # consequent de l'implication
    assert t.est_clos
