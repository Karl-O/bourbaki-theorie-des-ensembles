"""Tests — §III.4 PRINCIPE DE RÉCURRENCE (C61) par plus-petit-contre-exemple.

Vérifie :
  • principe_recurrence_P_pred(b,c) conclut EXACTEMENT principe_recurrence(_P_pred(b),c)
    (le REPORT #1 de N_collectivise_final), sous EXACTEMENT deux résidus honnêtes :
    predecesseur_fini_universel (Prop. 2 §III.5, gap maths) et bon_ordre_min_universel
    (≤-min du contre-exemple ; instance de cardinaux_bien_ordonnes_close bloquée comme
    résidu par une limitation de canonicalisation des liants du NOYAU) ;
  • la généricité (principe_recurrence_preuve marche pour un P quelconque) ;
  • A⊂[0,n0] est PROUVÉ (forme α-équivalente, _A_inclus_interv) ;
  • N_collectivise_report1_discharge ÉLIMINE le report #1, laissant {report#2, 2 résidus} ;
  • theorie_ensembles() == 22 (aucun axiome ajouté hors théories DÉDIÉES paramétrées).
"""
import pytest

from bourbaki.logique.formule import var, pourtout, impl, et, non, appartient, egal, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.entiers.ensembles_entiers import ZERO, est_fini, successeur
from bourbaki.entiers import ensembles_recurrence_C61 as C
import bourbaki.entiers.ensembles_principe_recurrence_preuve as M


# ── invariant THÉORIE = 22 ────────────────────────────────────────────────────
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── la cible : conclusion == principe_recurrence(_P_pred(b), c) LITTÉRALEMENT ──
def test_principe_P_pred_conclusion_est_la_cible():
    thm = M.principe_recurrence_P_pred("b", "c")
    assert thm.conclusion == C.principe_recurrence(C._P_pred("b"), "c")


# ── résidus EXACTS : {bon_ordre_min_universel, predecesseur_fini_universel} ────
def test_principe_P_pred_deux_residus_honnetes():
    thm = M.principe_recurrence_P_pred("b", "c")
    P = C._P_pred("b")
    attendus = {
        M.bon_ordre_min_universel(P, n0="n0pr"),
        M.predecesseur_fini_universel(k="kpred"),
    }
    assert set(thm.hypotheses) == attendus, \
        f"résidus inattendus : {[repr(h)[:80] for h in thm.hypotheses]}"
    assert len(thm.hypotheses) == 2


def test_principe_P_pred_non_vacueux():
    """La conclusion n'est PAS dans les hypothèses (preuve NON vacueuse)."""
    thm = M.principe_recurrence_P_pred("b", "c")
    assert thm.conclusion not in thm.hypotheses


# ── généricité : principe_recurrence_preuve marche pour un P arbitraire ────────
def test_principe_generique_pour_P_arbitraire():
    # P[t] := Fini(t)  (prédicat arbitraire, ≠ _P_pred)
    P = lambda t: est_fini(t)
    thm = M.principe_recurrence_preuve(P, "n")
    assert thm.conclusion == C.principe_recurrence(P, "n")
    # mêmes deux familles de résidus (instanciées à ce P)
    assert len(thm.hypotheses) == 2


# ── A ⊂ [0,n0] est PROUVÉ (forme α-équivalente, CLOSE) ────────────────────────
def test_A_inclus_interv_close():
    P = C._P_pred("b")
    vn0 = var("n0pr")
    asub = M._A_inclus_interv(P, vn0, "mApr")
    assert asub.est_clos
    assert asub.conclusion == inclus(M._A(P, vn0),
                                     E.intervalle_entiers(ZERO, vn0), "zincl")


# ── énoncés des résidus (formes attendues) ────────────────────────────────────
def test_predecesseur_fini_universel_forme():
    f = M.predecesseur_fini_universel(k="kpred")
    # (∀m)( (Fini m et m≠0) ⇒ (∃k)(m=k+1 et card k et k<m) )
    vm = var("mpred")
    assert f == pourtout("mpred",
        impl(et(est_fini(vm), non(egal(vm, ZERO))), M.predecesseur_fini(vm, "kpred")))


def test_bon_ordre_min_universel_ferme_en_n0():
    P = C._P_pred("b")
    f = M.bon_ordre_min_universel(P, n0="n0pr")
    # FERMÉ en n0 : aucune variable n0pr libre (c'est (∀n0pr)…)
    from bourbaki.logique.formule import libres_f
    assert "n0pr" not in libres_f(f)


# ── DÉCHARGE du report #1 de N_collectivise_final ─────────────────────────────
def test_report1_discharge_elimine_principe():
    disc = M.N_collectivise_report1_discharge()
    princ = C.principe_recurrence(C._P_pred("b"), "c")
    # report #1 ÉLIMINÉ
    assert princ not in disc.hypotheses
    # conclusion = coll(x, Fini x)  (ℕ existe)
    from bourbaki.entiers.ensembles_N_collectivise import _coll_fini
    assert disc.conclusion == _coll_fini("x")


def test_report1_discharge_residus_exacts():
    disc = M.N_collectivise_report1_discharge()
    P = C._P_pred("b")
    cpe = pourtout("c", pourtout("b", C.cardinal_pas_entre(var("b"), var("c"))))  # report #2
    bom = M.bon_ordre_min_universel(P, n0="n0pr")
    pred = M.predecesseur_fini_universel(k="kpred")
    assert set(disc.hypotheses) == {cpe, bom, pred}
    assert len(disc.hypotheses) == 3


def test_theorie_reste_22_apres_tout():
    M.principe_recurrence_P_pred("b", "c")
    M.N_collectivise_report1_discharge()
    assert len(E.theorie_ensembles().axiomes) == 22
