"""Tests — Chapitre III §1 : relations d'ordre, ensembles ordonnés (théorèmes directs)."""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, appartient, pourtout, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre as O


def _R(a, b):
    """Relation-test R{x,y} := (x,y)∈G (un graphe G fixé)."""
    G = var("G")
    return appartient(E.couple(a, b), G)


# ── §1.1, Exemple 3 — l'ordre opposé est un ordre ─────────────────────────────
def test_ordre_oppose_est_ordre():
    th = O.ordre_oppose_est_ordre(_R)
    assert th.est_clos
    cible = impl(E.est_relation_ordre(_R), E.est_relation_ordre(E.ordre_oppose(_R)))
    assert th.conclusion == cible


def test_preordre_oppose_est_preordre():
    th = O.preordre_oppose_est_preordre(_R)
    assert th.est_clos
    cible = impl(E.est_relation_preordre(_R), E.est_relation_preordre(E.ordre_oppose(_R)))
    assert th.conclusion == cible


# ── §1.7 — unicité du plus grand / plus petit élément ─────────────────────────
def test_unicite_plus_grand_element():
    th = O.unicite_plus_grand_element(_R)
    ve, va, vb = var("E"), var("a"), var("b")
    assert th.conclusion == egal(va, vb)
    attendues = {
        E.ordre_antisymetrique(_R, "x", "y"),
        E.est_plus_grand_element(_R, ve, va, "x"),
        E.est_plus_grand_element(_R, ve, vb, "x"),
    }
    assert th.hypotheses == attendues


def test_unicite_plus_petit_element():
    th = O.unicite_plus_petit_element(_R)
    ve, va, vb = var("E"), var("a"), var("b")
    assert th.conclusion == egal(va, vb)
    attendues = {
        E.ordre_antisymetrique(_R, "x", "y"),
        E.est_plus_petit_element(_R, ve, va, "x"),
        E.est_plus_petit_element(_R, ve, vb, "x"),
    }
    assert th.hypotheses == attendues


# ── §1.6-1.7 — plus grand ⟹ maximal, plus petit ⟹ minimal ────────────────────
def test_plus_grand_est_maximal():
    th = O.plus_grand_est_maximal(_R)
    ve, va = var("E"), var("a")
    assert th.conclusion == E.est_element_maximal(_R, ve, va, "x")
    attendues = {
        E.ordre_antisymetrique(_R, "x", "y"),
        E.est_plus_grand_element(_R, ve, va, "x"),
    }
    assert th.hypotheses == attendues


def test_plus_petit_est_minimal():
    th = O.plus_petit_est_minimal(_R)
    ve, va = var("E"), var("a")
    assert th.conclusion == E.est_element_minimal(_R, ve, va, "x")
    attendues = {
        E.ordre_antisymetrique(_R, "x", "y"),
        E.est_plus_petit_element(_R, ve, va, "x"),
    }
    assert th.hypotheses == attendues


# ── §1.8 — un minorant/majorant de X minore/majore toute partie de X ──────────
def test_minorant_partie():
    th = O.minorant_partie(_R)
    vX, vY, va = var("X"), var("Y"), var("a")
    assert th.conclusion == E.minore(_R, vY, va, "y")
    attendues = {E.minore(_R, vX, va, "y"), inclus(vY, vX)}
    assert th.hypotheses == attendues


def test_majorant_partie():
    th = O.majorant_partie(_R)
    vX, vY, va = var("X"), var("Y"), var("a")
    assert th.conclusion == E.majore(_R, vY, va, "y")
    attendues = {E.majore(_R, vX, va, "y"), inclus(vY, vX)}
    assert th.hypotheses == attendues


# ── Définitions bien formées (clôture / structure) ────────────────────────────
def test_definitions_bien_formees():
    G = var("G")
    e, a, b = var("E"), var("a"), var("b")
    # Termes/formules construits sans erreur, clos relativement aux paramètres.
    assert E.est_relation_ordre_dans(_R, e) is not None
    assert E.est_totalement_ordonne(_R, e) is not None
    assert E.sont_comparables(_R, a, b) is not None
    assert E.est_filtrant_droite(_R, e) is not None
    assert E.intervalle_ferme(_R, e, a, b) is not None
    assert E.est_cofinale(_R, var("A"), e) is not None
