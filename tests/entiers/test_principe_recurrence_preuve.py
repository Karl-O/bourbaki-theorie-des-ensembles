"""Tests — §III.4 PRINCIPE DE RÉCURRENCE (C61) par plus-petit-contre-exemple.

Vérifie :
  • principe_recurrence_P_pred(b,c) conclut EXACTEMENT principe_recurrence(_P_pred(b),c)
    (le REPORT #1 de N_collectivise_final), sous EXACTEMENT UN résidu honnête :
    predecesseur_fini_universel (Prop. 2 §III.5, vrai gap maths).  Le ≤-min du
    contre-exemple est DÉCHARGÉ via cardinaux_bien_ordonnes_close (CLOS), grâce au pont
    de liant _A_inclus_interv_raw (s7 sur ZERO@0=ZERO) — plus de résidu bon_ordre_min ;
  • la généricité (principe_recurrence_preuve marche pour un P quelconque) ;
  • A⊂[0,n0] est PROUVÉ (forme α-équivalente, _A_inclus_interv ; et forme RAW close
    _A_inclus_interv_raw qui décharge le min via cbo) ;
  • N_collectivise_report1_discharge ÉLIMINE le report #1, laissant {report#2, 1 résidu} ;
  • theorie_ensembles() == 22 (aucun axiome ajouté hors théories DÉDIÉES paramétrées).
"""
import pytest

from bourbaki.logique.formule import var, pourtout, impl, et, non, appartient, egal, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, est_fini, successeur
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n import ensembles_recurrence_C61 as C
import bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve as M


# ── invariant THÉORIE = 22 ────────────────────────────────────────────────────
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── la cible : conclusion == principe_recurrence(_P_pred(b), c) LITTÉRALEMENT ──
def test_principe_P_pred_conclusion_est_la_cible():
    thm = M.principe_recurrence_P_pred("b", "c")
    assert thm.conclusion == C.principe_recurrence(C._P_pred("b"), "c")


# ── résidu EXACT : {predecesseur_fini_universel} (bon_ordre_min DÉCHARGÉ via cbo) ──
def test_principe_P_pred_un_residu_honnete():
    thm = M.principe_recurrence_P_pred("b", "c")
    attendus = {
        M.predecesseur_fini_universel(k="kpred"),
    }
    assert set(thm.hypotheses) == attendus, \
        f"résidus inattendus : {[repr(h)[:80] for h in thm.hypotheses]}"
    assert len(thm.hypotheses) == 1


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
    # même résidu unique (bon_ordre_min déchargé via cbo, pour tout P)
    assert len(thm.hypotheses) == 1


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


def test_bon_ordre_min_decharge_via_cbo():
    """Le ≤-min du contre-exemple est DÉCHARGÉ via cardinaux_bien_ordonnes_close :
    le pont de liant _A_inclus_interv_raw est CLOS, et bon_ordre_min n'est PLUS un résidu."""
    P = C._P_pred("b")
    raw = M._A_inclus_interv_raw(P, "n0pr")
    assert raw.est_clos, "le pont de liant _A_inclus_interv_raw doit être CLOS (0 hyp)"
    thm = M.principe_recurrence_P_pred("b", "c")
    assert M.bon_ordre_min_universel(P, n0="n0pr") not in set(thm.hypotheses)


# ── DÉCHARGE du report #1 de N_collectivise_final ─────────────────────────────
def test_report1_discharge_elimine_principe():
    disc = M.N_collectivise_report1_discharge()
    princ = C.principe_recurrence(C._P_pred("b"), "c")
    # report #1 ÉLIMINÉ
    assert princ not in disc.hypotheses
    # conclusion = coll(x, Fini x)  (ℕ existe)
    from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import _coll_fini
    assert disc.conclusion == _coll_fini("x")


def test_report1_discharge_residus_exacts():
    disc = M.N_collectivise_report1_discharge()
    cpe = pourtout("c", pourtout("b", C.cardinal_pas_entre(var("b"), var("c"))))  # report #2
    pred = M.predecesseur_fini_universel(k="kpred")
    assert set(disc.hypotheses) == {cpe, pred}
    assert len(disc.hypotheses) == 2


def test_theorie_reste_22_apres_tout():
    M.principe_recurrence_P_pred("b", "c")
    M.N_collectivise_report1_discharge()
    assert len(E.theorie_ensembles().axiomes) == 22
