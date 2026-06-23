"""Tests §III.3.5 — Proposition 9 (forme exponentielle) a^(b+c) = a^b · a^c.

PALIERS CERTIFIÉS (round 25) : la RESTRICTION f ↦ (f|B, f|C) et le RECOLLEMENT
(g,h) ↦ g∪h, les deux demi-constructions de la bijection Φ.  La bijection complète
(injectivité/surjectivité par extensionnalité fonctionnelle réindexée) est REPORTÉE.

Tout est DÉRIVÉ de l'infra round 24/25 (graphe-terme C54, recollement) + des
axiomes de DÉFINITION — rien postulé.
"""
import pytest
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, appartient, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, ZERO, UN)
from bourbaki.cardinaux.arithmetique import ensembles_prop9_exp_somme as P


# ── PALIER 0 : ÉNONCÉ-CIBLE (formule) ────────────────────────────────────────
def test_cible_prop9_exp_somme_forme():
    """La cible Card(𝓕(B⊔C;A)) = Card(𝓕(B;A) × 𝓕(C;A))  (forme exacte)."""
    vA, vB, vC = var("A"), var("B"), var("C")
    BC = somme_disjointe(vB, vC)
    cible = P.cible_prop9_exp_somme("A", "B", "C")
    gauche = cardinal(E.applications(BC, vA))
    droite = cardinal(E.produit(E.applications(vB, vA), E.applications(vC, vA)))
    assert cible == egal(gauche, droite)


# ── PALIER R : RESTRICTION f ↦ f|B (copie gauche, indice 0) ──────────────────
def test_restriction_gauche_terme_forme():
    """f|B := graphe_terme(B, f((e,0)))  (terme, forme exacte)."""
    vf, vB = var("f"), var("B")
    fB = P.restriction_gauche("f", "B")
    val = E.valeur(vf, E.couple(var("e"), ZERO), "c")     # f((e,0)), liant exotique « c »
    assert fB == E.graphe_terme(vB, val, "e")


def test_restriction_gauche_fonctionnelle():
    """⊢ est_fonctionnel(f|B), CLOS  (f|B est une vraie fonction ; C54)."""
    th = P.restriction_gauche_fonctionnelle("f", "B")
    assert th.conclusion == E.est_fonctionnel(P.restriction_gauche("f", "B"))
    assert th.est_clos


def test_restriction_gauche_domaine():
    """⊢ dom(f|B) = B, CLOS  (la restriction est définie sur toute la copie B)."""
    th = P.restriction_gauche_domaine("f", "B")
    assert th.conclusion == egal(E.dom(P.restriction_gauche("f", "B")), var("B"))
    assert th.est_clos


def test_restriction_gauche_valeur():
    """{u∈B} ⊢ (f|B)(u) = f((u,0))  (valeur de la restriction gauche en u)."""
    vf, vB, vu = var("f"), var("B"), var("u")
    th = P.restriction_gauche_valeur("f", "B", "u")
    val = E.valeur(vf, E.couple(vu, ZERO), "c")           # f((u,0))
    assert th.conclusion == egal(E.valeur(P.restriction_gauche("f", "B"), vu), val)
    # théorème conditionnel : il porte l'hypothèse u∈B
    assert appartient(vu, vB) in th.hypotheses


# ── PALIER R : RESTRICTION f ↦ f|C (copie droite, indice 1) ──────────────────
def test_restriction_droite_terme_forme():
    """f|C := graphe_terme(C, f((e,1)))  (terme, forme exacte)."""
    vf, vC = var("f"), var("C")
    fC = P.restriction_droite("f", "C")
    val = E.valeur(vf, E.couple(var("e"), UN), "c")       # f((e,1))
    assert fC == E.graphe_terme(vC, val, "e")


def test_restriction_droite_fonctionnelle():
    """⊢ est_fonctionnel(f|C), CLOS."""
    th = P.restriction_droite_fonctionnelle("f", "C")
    assert th.conclusion == E.est_fonctionnel(P.restriction_droite("f", "C"))
    assert th.est_clos


def test_restriction_droite_domaine():
    """⊢ dom(f|C) = C, CLOS."""
    th = P.restriction_droite_domaine("f", "C")
    assert th.conclusion == egal(E.dom(P.restriction_droite("f", "C")), var("C"))
    assert th.est_clos


def test_restriction_droite_valeur():
    """{v∈C} ⊢ (f|C)(v) = f((v,1))  (valeur de la restriction droite ; point « m »)."""
    vf, vC, vm = var("f"), var("C"), var("m")
    th = P.restriction_droite_valeur("f", "C", "m")
    val = E.valeur(vf, E.couple(vm, UN), "c")             # f((m,1))
    assert th.conclusion == egal(E.valeur(P.restriction_droite("f", "C"), vm), val)
    assert appartient(vm, vC) in th.hypotheses


def test_restriction_point_interdit():
    """Garde-fou : un point d'évaluation qui collisionne un liant interne est refusé."""
    with pytest.raises(ValueError):
        P.restriction_gauche_valeur("f", "B", "v")        # « v » = liant interne
    with pytest.raises(ValueError):
        P.restriction_droite_valeur("f", "C", "e")        # « e » = liant du graphe


# ── PALIER G : RECOLLEMENT (g,h) ↦ g∪h (inverse de Φ) ────────────────────────
def test_recollement_terme_forme():
    """g∪h := recollement(g,h) = g ∪ h  (terme, forme exacte)."""
    vg, vh = var("G"), var("H")
    assert P.recollement_gauche_droite("G", "H") == E.reunion(vg, vh)


def test_recollement_fonctionnel():
    """⊢ (G fonct et H fonct et domG⊂B×{0} et domH⊂C×{1}) ⇒ est_fonctionnel(G∪H), CLOS.

    Deux graphes fonctionnels portés par les copies marquées DISJOINTES se recollent
    en une fonction sur B⊔C (0≠1 sépare les copies) — l'inverse de Φ."""
    vg, vh, vB, vC = var("G"), var("H"), var("B"), var("C")
    th = P.recollement_fonctionnel("G", "H", "B", "C")
    B0 = E.produit(vB, E.singleton(ZERO))
    C1 = E.produit(vC, E.singleton(UN))
    hyp = et(et(et(E.est_fonctionnel(vg), E.est_fonctionnel(vh)),
                inclus(E.dom(vg), B0)), inclus(E.dom(vh), C1))
    assert th.conclusion == impl(hyp, E.est_fonctionnel(E.reunion(vg, vh)))
    assert th.est_clos


# ── CŒUR REPORTÉ : la bijection Φ complète ───────────────────────────────────
def test_bijection_phi_reporte():
    """La bijection Φ complète (et l'égalité-cible) est honnêtement REPORTÉE."""
    with pytest.raises(NotImplementedError):
        P.bijection_phi_REPORTE()
