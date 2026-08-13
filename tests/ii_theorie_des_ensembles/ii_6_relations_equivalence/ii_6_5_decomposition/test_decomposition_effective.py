"""Tests V9 — §II.6 : décomposition canonique EFFECTIVE, injectivité de b.

Vérifient le CŒUR (passage au quotient INCONDITIONNEL : f(x)=f(y) ⇒ Cl(x)=Cl(y)) et
l'injectivité de la bijection induite b via le PONT (b(Cl(x))=f(x)) : conclusions
LITTÉRALES + jeu d'hypothèses EXACT + clôture (.est_clos) du cœur.  theorie=22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, tau, egal, et, impl, appartient, pourtout)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition import ensembles_decomposition_effective as D

# liants frais utilisés par le module (verrou liant valeur) — à refléter dans les
# formules de référence des tests.
_VF, _VB = D._VF, D._VB


def _vf(vf, x):
    return E.valeur(vf, x, b=_VF)            # f(x), liant frais


def _vb(vb, t):
    return E.valeur(vb, t, b=_VB)            # b(t), liant frais


def _theta(vf, vx, ve, w="w"):
    """θ_{R_f}(x) = τ_w((x∈E et w∈E) et f(x)=f(w))  (référence pour les tests, liant f frais)."""
    vw = var(w)
    corps = et(et(appartient(vx, ve), appartient(vw, ve)),
               egal(_vf(vf, vx), _vf(vf, vw)))
    return tau(w, corps)


# ════════════════════════════════════════════════════════════════════════════
# 0.  Classe d'objets θ_{R_f}(x)
# ════════════════════════════════════════════════════════════════════════════
def test_classe_objets_Rf_def():
    """θ_{R_f}(x) = τ_w((x∈dom f et w∈dom f) et f(x)=f(w))  (E.II.6.9, verbatim)."""
    vf, vx = var("f"), var("x")
    assert D.classe_objets_Rf(vf, vx) == _theta(vf, vx, E.dom(vf))


def test_classe_objets_Rf_e_explicite():
    """E paramétré : la classe utilise bien le E fourni."""
    vf, vx, vE = var("f"), var("x"), var("E")
    assert D.classe_objets_Rf(vf, vx, e=vE) == _theta(vf, vx, vE)


# ════════════════════════════════════════════════════════════════════════════
# 1.  CŒUR INCONDITIONNEL : f(x)=f(y) ⇒ Cl(x)=Cl(y)
# ════════════════════════════════════════════════════════════════════════════
def test_passage_quotient_Rf_conclusion():
    """⊢ ((x∈E et y∈E) et f(x)=f(y)) ⇒ θ(x)=θ(y)  (conclusion littérale)."""
    vf, vx, vy = var("f"), var("x"), var("y")
    vE = var("E")
    t = D.passage_quotient_Rf("f", vE, "x", "y")
    fx, fy = _vf(vf, vx), _vf(vf, vy)
    ante = et(et(appartient(vx, vE), appartient(vy, vE)), egal(fx, fy))
    cible = impl(ante, egal(_theta(vf, vx, vE), _theta(vf, vy, vE)))
    assert t.conclusion == cible


def test_passage_quotient_Rf_clos():
    """Le cœur est INCONDITIONNEL : 0 hypothèse, est_clos."""
    t = D.passage_quotient_Rf("f", var("E"), "x", "y")
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_passage_quotient_Rf_dom_par_defaut():
    """E = dom f par défaut ; toujours clos."""
    vf, vx, vy = var("f"), var("x"), var("y")
    t = D.passage_quotient_Rf("f")
    ante = et(et(appartient(vx, E.dom(vf)), appartient(vy, E.dom(vf))),
              egal(_vf(vf, vx), _vf(vf, vy)))
    cible = impl(ante, egal(_theta(vf, vx, E.dom(vf)), _theta(vf, vy, E.dom(vf))))
    assert t.conclusion == cible and t.est_clos


# ════════════════════════════════════════════════════════════════════════════
# 2.  INJECTIVITÉ de b au niveau des valeurs (via le PONT)
# ════════════════════════════════════════════════════════════════════════════
def test_b_injective_valeurs_conclusion():
    """{b(θx)=f(x), b(θy)=f(y)} ⊢ ((x∈E et y∈E) et b(θx)=b(θy)) ⇒ θx=θy."""
    vf, vb, vE = var("f"), var("b"), var("E")
    vx, vy = var("x"), var("y")
    t = D.b_injective_valeurs("f", "b", vE, "x", "y")
    thx, thy = _theta(vf, vx, vE), _theta(vf, vy, vE)
    bx, by = _vb(vb, thx), _vb(vb, thy)
    ante = et(et(appartient(vx, vE), appartient(vy, vE)), egal(bx, by))
    cible = impl(ante, egal(thx, thy))
    assert t.conclusion == cible


def test_b_injective_valeurs_hypotheses():
    """Hypothèses EXACTES = les 2 relations de valeur du pont (rien d'autre)."""
    vf, vb, vE = var("f"), var("b"), var("E")
    vx, vy = var("x"), var("y")
    t = D.b_injective_valeurs("f", "b", vE, "x", "y")
    thx, thy = _theta(vf, vx, vE), _theta(vf, vy, vE)
    bx, by = _vb(vb, thx), _vb(vb, thy)
    fx, fy = _vf(vf, vx), _vf(vf, vy)
    assert t.hypotheses == frozenset({egal(bx, fx), egal(by, fy)})
    assert not t.est_clos


def test_relation_valeur_b_def():
    """b(θ(x)) = f(x)  (forme de la relation de valeur du pont)."""
    vf, vb, vE, vx = var("f"), var("b"), var("E"), var("x")
    h = D.relation_valeur_b(vf, vb, vx, e=vE)
    assert h == egal(_vb(vb, _theta(vf, vx, vE)), _vf(vf, vx))


# ════════════════════════════════════════════════════════════════════════════
# 3.  INJECTIVITÉ de b en forme injective_dans (conditionnée au PONT universel)
# ════════════════════════════════════════════════════════════════════════════
def test_pont_valeurs_b_def():
    """(∀x)(x∈E ⇒ b(θ(x))=f(x))  (le pont universel)."""
    vf, vb, vE, vx = var("f"), var("b"), var("E"), var("x")
    h = D.pont_valeurs_b(vf, vb, e=vE)
    cible = pourtout("x", impl(appartient(vx, vE),
                               egal(_vb(vb, _theta(vf, vx, vE)), _vf(vf, vx))))
    assert h == cible


def test_b_injective_via_pont_conclusion():
    """{pont} ⊢ (∀x)(∀y)(((x∈E et y∈E) et b(θx)=b(θy)) ⇒ θx=θy)."""
    vf, vb, vE = var("f"), var("b"), var("E")
    vx, vy = var("x"), var("y")
    t = D.b_injective_via_pont("f", "b", vE, "x", "y")
    thx, thy = _theta(vf, vx, vE), _theta(vf, vy, vE)
    bx, by = _vb(vb, thx), _vb(vb, thy)
    ante = et(et(appartient(vx, vE), appartient(vy, vE)), egal(bx, by))
    cible = pourtout("x", pourtout("y", impl(ante, egal(thx, thy))))
    assert t.conclusion == cible


def test_b_injective_via_pont_hypotheses():
    """Hypothèse EXACTE = le pont universel uniquement."""
    vf, vb, vE = var("f"), var("b"), var("E")
    t = D.b_injective_via_pont("f", "b", vE, "x", "y")
    assert t.hypotheses == frozenset({D.pont_valeurs_b(vf, vb, e=vE)})
    assert not t.est_clos
