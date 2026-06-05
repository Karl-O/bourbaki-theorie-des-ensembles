"""Tests — Chapitre III §2 : ensembles bien ordonnés (définitions + théorèmes directs).

Chaque théorème est vérifié sur sa CIBLE EXACTE + clôture (ou hypothèses attendues).
"""
from __future__ import annotations

from formule import var, egal, et, impl, ou, non, appartient, inclus, pourtout, existe
import ensembles_abrege as E
import ensembles_bon_ordre as BO


def _R(a, b):
    """Relation-test R{x,y} := (x,y)∈G (un graphe G fixé), R notée ≤."""
    G = var("G")
    return appartient(E.couple(a, b), G)


# ── Définition 1 — un ensemble bien ordonné est ordonné ───────────────────────
def test_bien_ordonne_est_ordonne():
    th = BO.bien_ordonne_est_ordonne(_R)
    assert th.est_clos
    e = var("E")
    cible = impl(E.est_bien_ordonne(_R, e), E.est_relation_ordre_dans(_R, e))
    assert th.conclusion == cible


# ── Définition 2 — segments triviaux ──────────────────────────────────────────
def test_ensemble_est_segment():
    th = BO.ensemble_est_segment(_R)
    assert th.est_clos
    e = var("E")
    assert th.conclusion == E.est_segment(e, _R, e)


def test_vide_est_segment():
    th = BO.vide_est_segment(_R)
    assert th.est_clos
    e = var("E")
    assert th.conclusion == E.est_segment(E.VIDE, _R, e)


def test_segment_inclus():
    th = BO.segment_inclus(_R)
    assert th.est_clos
    S, e = var("S"), var("E")
    cible = impl(E.est_segment(S, _R, e), inclus(S, e))
    assert th.conclusion == cible


# ── Clôture par intersection / réunion ────────────────────────────────────────
def test_intersection_segments_segment():
    th = BO.intersection_segments_segment(_R)
    assert th.est_clos
    A, B, e = var("A"), var("B"), var("E")
    cible = impl(et(E.est_segment(A, _R, e), E.est_segment(B, _R, e)),
                 E.est_segment(E.intersection(A, B), _R, e))
    assert th.conclusion == cible


def test_reunion_segments_segment():
    th = BO.reunion_segments_segment(_R)
    assert th.est_clos
    A, B, e = var("A"), var("B"), var("E")
    cible = impl(et(E.est_segment(A, _R, e), E.est_segment(B, _R, e)),
                 E.est_segment(E.reunion(A, B), _R, e))
    assert th.conclusion == cible


# ── Définitions bien formées (clôture / structure) ────────────────────────────
def test_definitions_bien_formees():
    e, x, a = var("E"), var("x"), var("a")
    assert E.est_bien_ordonne(_R, e) is not None
    assert E.est_relation_bon_ordre(_R, e) == E.est_bien_ordonne(_R, e)
    assert E.est_segment(var("S"), _R, e) is not None
    assert E.segment_extremite(_R, e, x) is not None
    assert E.est_majorant_strict(_R, var("X"), a) is not None
    assert E.est_inductif(_R, e) is not None
    # axiome de S_x : équivalence universellement quantifiée bien formée
    ax = E.axiome_segment_extremite(_R)
    assert ax.tag == "non"  # (∀…) est ¬∃¬…
    assert E.theorie_segment_extremite(_R) is not None
