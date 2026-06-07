"""Tests de ensembles_zorn.py — vocabulaire fidèle §III.2 + lemmes directs.

Chaque test vérifie la conclusion EXACTE produite par le noyau abrégé et les
hypothèses résiduelles (les lemmes ouverts gardent leurs hypothèses ; les
définitions se construisent bien et coïncident avec la forme Bourbaki).
"""
from bourbaki.logique.formule import (
    var, et, impl, appartient, pourtout, existe, inclus,
)
from bourbaki.ordre import ensembles_ordre_relation as O
from bourbaki.ordre import ensembles_zorn as Z


G, Es, C, A = var("G"), var("E"), var("C"), var("A")
m, a = var("m"), var("a")


# ── Définitions fidèles §III.2 : se construisent et coïncident avec Bourbaki ───
def test_chaine_definition():
    f = Z.chaine(G, Es, C)
    assert f is not None
    # chaine(G,E,C) = (C⊂E) et totalement_ordonne(G,C)
    cible = et(inclus(C, Es), O.totalement_ordonne(G, C))
    assert f == cible


def test_est_inductif_definition():
    f = Z.est_inductif(G, Es)
    assert f is not None
    # est_inductif = est_ordre(G,E) et (∀C)(chaine(G,E,C) ⇒ (∃m)majorant(G,C,m,E))
    corps = impl(Z.chaine(G, Es, var("C")),
                 existe("m", O.majorant(G, var("C"), m, Es)))
    cible = et(O.est_ordre(G, Es), pourtout("C", corps))
    assert f == cible


def test_enonce_non_vide_definition():
    f = Z.enonce_non_vide(Es)
    assert f == existe("x", appartient(var("x"), Es))


def test_zorn_enonce_definition():
    f = Z.zorn(G, Es)
    assert f is not None
    # zorn = (est_ordre et est_inductif et E≠∅) ⇒ (∃m)element_maximal(G,E,m)
    hyp = et(et(O.est_ordre(G, Es), Z.est_inductif(G, Es)), Z.enonce_non_vide(Es))
    cible = impl(hyp, existe("m", O.element_maximal(G, Es, m)))
    assert f == cible


# ── Lemmes directs : décomposition des définitions ────────────────────────────
def test_chaine_est_partie():
    t = Z.chaine_est_partie("G", "E", "C")
    assert t.conclusion == inclus(C, Es)
    assert t.hypotheses == {Z.chaine(G, Es, C)}


def test_chaine_est_totalement_ordonnee():
    t = Z.chaine_est_totalement_ordonnee("G", "E", "C")
    assert t.conclusion == O.totalement_ordonne(G, C)
    assert t.hypotheses == {Z.chaine(G, Es, C)}


def test_inductif_est_ordre():
    t = Z.inductif_est_ordre("G", "E")
    assert t.conclusion == O.est_ordre(G, Es)
    assert t.hypotheses == {Z.est_inductif(G, Es)}


def test_inductif_chaine_majoree():
    t = Z.inductif_chaine_majoree("G", "E", "C")
    # chaine(G,E,C) ⇒ (∃m)majorant(G,C,m,E)
    cible = impl(Z.chaine(G, Es, C), existe("m", O.majorant(G, C, m, Es)))
    assert t.conclusion == cible
    assert t.hypotheses == {Z.est_inductif(G, Es)}


# ── Théorème direct : plus grand élément ⇒ (∃m) élément maximal (conclusion Zorn)
def test_plus_grand_donne_maximal_existe():
    t = Z.plus_grand_donne_maximal_existe("G", "E")
    assert t.conclusion == existe("m", O.element_maximal(G, Es, m))
    assert t.hypotheses == {O.antisymetrie(G), O.plus_grand_element(G, Es, m)}


def test_zorn_si_plus_grand_element():
    t = Z.zorn_si_plus_grand_element("G", "E")
    assert t.conclusion == existe("m", O.element_maximal(G, Es, m))
    assert t.hypotheses == {O.antisymetrie(G), O.plus_grand_element(G, Es, m)}
