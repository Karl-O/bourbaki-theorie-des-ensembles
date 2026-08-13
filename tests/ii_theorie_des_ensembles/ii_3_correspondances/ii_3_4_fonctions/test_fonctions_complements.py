"""Tests §II.3 — Micro-notions complémentaires (coupe, permutation, fonction de
deux arguments, applications partielles, correspondance réciproque/composée).

Chaque notion : on vérifie que le TERME / PRÉDICAT construit est EXACTEMENT
l'assemblage fidèle attendu ; le seul lemme prouvé (coupe_caracterisation) est
vérifié sur sa conclusion ET sa clôture. theorie_ensembles() reste à 22 axiomes.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, appartient, inclus, equiv
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_fondations_notions import (
    correspondance, est_application,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions import ensembles_fonctions_complements as C


def test_coupe_terme():
    vG, vx = var("G"), var("x")
    assert C.coupe(vG, vx) == E.image(vG, E.singleton(vx))


def test_coupe_caracterisation():
    vG, va, vy = var("G"), var("a"), var("y")
    t = C.coupe_caracterisation()
    cible = equiv(appartient(vy, E.image(vG, E.singleton(va))),
                  appartient(E.couple(va, vy), vG))
    assert t.conclusion == cible
    assert t.est_clos


def test_est_permutation():
    vF, vA = var("F"), var("A")
    assert C.est_permutation(vF, vA) == E.est_bijective(vF, vA, vA)


def test_est_permutation_triple():
    vF, vA = var("F"), var("A")
    cible = et(est_application(vF, vA, vA), E.est_bijective(vF, vA, vA))
    assert C.est_permutation_triple(vF, vA) == cible


def test_est_fonction_deux_arguments():
    vF, vA, vB = var("F"), var("A"), var("B")
    cible = et(E.est_fonctionnel(vF), inclus(E.dom(vF), E.produit(vA, vB)))
    assert C.est_fonction_deux_arguments(vF, vA, vB) == cible


def test_valeur_deux_arguments():
    vF, vx, vy = var("F"), var("x"), var("y")
    assert C.valeur_deux_arguments(vF, vx, vy) == E.valeur(vF, E.couple(vx, vy))


def test_application_partielle_seconde():
    vF, vA, vC, vy0, vx = var("F"), var("A"), var("C"), var("y0"), var("x")
    T = E.valeur(vF, E.couple(vx, vy0))
    cible = E.fonction_terme(vA, T, vC, "x")
    assert C.application_partielle_seconde(vF, vA, vC, vy0) == cible


def test_application_partielle_seconde_terme():
    vF, vy0, vx = var("F"), var("y0"), var("x")
    assert C.application_partielle_seconde_terme(vF, vy0) == E.valeur(vF, E.couple(vx, vy0))


def test_application_partielle_premiere_terme():
    vF, vx0, vy = var("F"), var("x0"), var("y")
    assert C.application_partielle_premiere_terme(vF, vx0) == E.valeur(vF, E.couple(vx0, vy))


def test_correspondance_reciproque():
    vG, vA, vB = var("G"), var("A"), var("B")
    cible = correspondance(E.reciproque(vG), vB, vA)
    assert C.correspondance_reciproque(vG, vA, vB) == cible


def test_correspondance_composee_simple():
    vH, vG, vA, vC = var("H"), var("G"), var("A"), var("C")
    cible = correspondance(E.composee(vH, vG), vA, vC)
    assert C.correspondance_composee_simple(vH, vG, vA, vC) == cible


def test_correspondance_composee():
    vH, vG, vA, vB, vC = var("H"), var("G"), var("A"), var("B"), var("C")
    cible = correspondance(E.composee(vH, vG), vA, vC)
    assert C.correspondance_composee(vH, vB, vC, vG, vA, vB) == cible


def test_theorie_22_axiomes():
    th = E.theorie_ensembles()
    assert len(th.axiomes) == 22
