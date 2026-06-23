"""Tests — §III.2 : RÉCURRENCE TRANSFINIE (Critère C59) par plus-petit-contre-exemple.

Vérifie le MÉTATHÉORÈME `recurrence_transfinie_preuve(P)` sur sa CIBLE EXACTE :
    est_bien_ordonne(R,E) ⇒ ( heredite_transfinie(P,R,E) ⇒ conclusion_transfinie(P,E) )
clos (0 hypothèse), non vacuous, theorie_ensembles() = 22 intangible, et GÉNÉRIQUE
sur le prédicat P (fonction Python Terme→Formule).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, app, egal, et, non, impl, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie import ensembles_recurrence_transfinie as TF


def _R(a, b):
    """Relation-test R{x,y} := (x,y)∈G  (un graphe G fixé), R notée ≤."""
    return appartient(E.couple(a, b), var("G"))


def _P(t):
    """Prédicat-test P[t] := t ∈ Pset  (symbolique, via membership)."""
    return appartient(t, var("Pset"))


# ── théorie intangible ────────────────────────────────────────────────────────
def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── énoncés bien formés ───────────────────────────────────────────────────────
def test_enonces_bien_formes():
    e = var("E")
    assert TF.heredite_transfinie(_P, _R, e) is not None
    assert TF.conclusion_transfinie(_P, e) is not None
    assert TF.recurrence_transfinie(_P, _R, e) is not None


# ── MÉTATHÉORÈME C59 : CLOS, 0 hypothèse ──────────────────────────────────────
def test_recurrence_transfinie_close():
    th = TF.recurrence_transfinie_preuve(_P)
    assert th.est_clos
    assert len(th.hypotheses) == 0


# ── conclusion == énoncé EXACT (binders effectifs x0='x0tf', y='ytf') ─────────
def test_conclusion_exacte():
    th = TF.recurrence_transfinie_preuve(_P)
    e = var("E")
    cible = TF.recurrence_transfinie(_P, _R, e, "x0tf", "ytf")
    assert th.conclusion == cible


# ── structure : W ⇒ (hérédité ⇒ conclusion) ───────────────────────────────────
def test_structure_implication():
    th = TF.recurrence_transfinie_preuve(_P)
    e = var("E")
    c = th.conclusion                       # impl = ¬∨
    assert c.tag == "ou" and c.sous[0].tag == "non"
    ante = c.sous[0].sous[0]
    cons = c.sous[1]
    assert ante == E.est_bien_ordonne(_R, e)             # antécédent = bon ordre
    h = cons.sous[0].sous[0]
    k = cons.sous[1]
    assert h == TF.heredite_transfinie(_P, _R, e, "x0tf", "ytf")
    assert k == TF.conclusion_transfinie(_P, e, "x0tf")


# ── NON-VACUITÉ : conclusion ∉ hypothèses ; ante ≠ cons ; hérédité ≠ conclusion ─
def test_non_vacuous():
    th = TF.recurrence_transfinie_preuve(_P)
    assert th.conclusion not in th.hypotheses
    c = th.conclusion
    ante = c.sous[0].sous[0]
    cons = c.sous[1]
    assert ante != cons
    h = cons.sous[0].sous[0]
    k = cons.sous[1]
    assert h != k


# ── GÉNÉRICITÉ : marche pour d'autres prédicats P ─────────────────────────────
def test_generique_predicat_egalite():
    def P2(t):
        return non(egal(t, app("foo")))
    th = TF.recurrence_transfinie_preuve(P2)
    assert th.est_clos and len(th.hypotheses) == 0


def test_generique_predicat_compose():
    def P3(t):
        return et(appartient(t, var("S1")), appartient(t, var("S2")))
    th = TF.recurrence_transfinie_preuve(P3)
    assert th.est_clos and len(th.hypotheses) == 0


# ══════════════════════════════════════════════════════════════════════════════
#  C60 — DÉFINITION PAR RÉCURRENCE TRANSFINIE : UNICITÉ (corollaire de C59).
# ══════════════════════════════════════════════════════════════════════════════
def _vf(x):
    return E.valeur(var("Ff"), x)


def _vg(x):
    return E.valeur(var("Fg"), x)


def test_c60_unicite_enonces_bien_formes():
    e = var("E")
    assert TF.regle_coherente_sur_segments(_vf, _vg, _R, e) is not None
    assert TF.coincidence_solutions(_vf, _vg, e) is not None


def test_c60_unicite_sous_deux_hyps_honnetes():
    th = TF.recursion_transfinie_unicite(_vf, _vg)
    # NON inconditionnel : EXACTEMENT 2 hypothèses honnêtes (bon ordre + cohérence-règle)
    assert len(th.hypotheses) == 2
    e = var("E")
    assert E.est_bien_ordonne(_R, e) in th.hypotheses
    assert TF.regle_coherente_sur_segments(_vf, _vg, _R, e, "x0tf", "ytf") in th.hypotheses


def test_c60_unicite_conclusion_exacte():
    th = TF.recursion_transfinie_unicite(_vf, _vg)
    e = var("E")
    assert th.conclusion == TF.coincidence_solutions(_vf, _vg, e, "x0tf")


def test_c60_unicite_non_vacuous():
    th = TF.recursion_transfinie_unicite(_vf, _vg)
    # la conclusion (coïncidence) n'est PAS l'une des hypothèses (P⇒P interdit)
    assert th.conclusion not in th.hypotheses
