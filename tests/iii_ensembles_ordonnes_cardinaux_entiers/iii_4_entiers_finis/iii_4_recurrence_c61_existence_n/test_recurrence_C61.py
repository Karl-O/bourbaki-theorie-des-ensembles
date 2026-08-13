"""Tests §III.4 — RÉCURRENCE (C61) & fini_downward : clôture (conditionnelle) de ℕ.

Discipline LCF stricte : chaque test vérifie la CONCLUSION EXACTE et l'ensemble des
HYPOTHÈSES (clos pour les paliers INCONDITIONNELS ; reports précis pour la chaîne).

INVARIANT vérifié partout : theorie_ensembles() = 22 (aucun axiome nouveau ; les
seules théories dédiées importées — intervalle, Ncol — restent hors theorie_ensembles).

PALIERS :
  ✅ INCONDITIONNELS (.est_clos) : b_le_0_implique_egal_0, base_P0.
  ⚙️ STRUCTURE (reports isolés) : pas_recurrence (sous cardinal_pas_entre),
     recurrence_C61 (métathéorème), fini_downward_thm + N_collectivise_final
     (sous les DEUX reports principe_recurrence + cardinal_pas_entre).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, coll, pourtout, impl, et, ou, egal, non, appartient, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, ZERO, successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import fini_downward
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n import ensembles_recurrence_C61 as C


# ── INVARIANT : theorie_ensembles() intangible = 22 ──────────────────────────
def test_theorie_ensembles_reste_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── ÉTAPE 3 — BASE (INCONDITIONNELLE) ─────────────────────────────────────────
def test_b_le_0_implique_egal_0_clos():
    """⊢ ( b ≤ 0 ) ⇒ ( b = 0 )   — CLOS (seul ∅ s'injecte dans ∅)."""
    vb = var("b")
    thm = C.b_le_0_implique_egal_0("b")
    assert thm.est_clos
    assert thm.conclusion == impl(inf_egal_card(vb, ZERO), egal(vb, ZERO))


def test_base_P0_clos():
    """⊢ ( b ≤ 0 ) ⇒ Fini(b)   — BASE P[0], CLOS (INCONDITIONNEL)."""
    vb = var("b")
    thm = C.base_P0("b")
    assert thm.est_clos
    assert thm.conclusion == impl(inf_egal_card(vb, ZERO), est_fini(vb))


def test_preuve_P0_universel_clos():
    """⊢ P[0] = (∀b)( b ≤ 0 ⇒ Fini b )   — CLOS."""
    vb = var("b")
    thm = C._preuve_P0("b")
    assert thm.est_clos
    assert thm.conclusion == pourtout("b", impl(inf_egal_card(vb, ZERO), est_fini(vb)))


# ── ÉTAPE 3 — PAS (conditionné au SOUS-LEMME cardinal_pas_entre) ──────────────
def test_pas_recurrence_conclusion_et_report():
    """⊢ { (∀b)cardinal_pas_entre(b,c) } ⊢ ( P[c] ⇒ P[c+1] )."""
    vc, vb = var("c"), var("b")
    thm = C.pas_recurrence("c", "b")
    Pc = C._P(vc, "b")
    Pc1 = C._P(successeur(vc), "b")
    assert thm.conclusion == impl(Pc, Pc1)
    # unique report : (∀b) « pas de cardinal entre c et c+1 »
    assert set(thm.hypotheses) == {pourtout("b", C.cardinal_pas_entre(vb, vc))}


# ── ÉTAPE 2 — C61 (métathéorème) ──────────────────────────────────────────────
def test_recurrence_C61_metatheoreme():
    """recurrence_C61(⊢P[0], ⊢pas, P) ⊢ (∀n)(Fini n ⇒ P[n]) sous principe_recurrence(P).

    Vérifié sur le PRÉDICAT RÉEL P[c] := (∀b)(b≤c ⇒ Fini b) avec les VRAIES preuves
    (base inconditionnelle + pas conditionné au sous-lemme)."""
    P = C._P_pred("b")
    p0 = C._preuve_P0("b")
    step = C._preuve_step("c", "b")
    res = C.recurrence_C61(p0, step, P, "c")
    assert res.conclusion == C._fini_implique_P(P, "c")
    # reports : principe_recurrence(P)  +  (∀c)(∀b)cardinal_pas_entre(b,c)
    vc, vb = var("c"), var("b")
    attendus = {
        C.principe_recurrence(P, "c"),
        pourtout("c", pourtout("b", C.cardinal_pas_entre(vb, vc))),
    }
    assert set(res.hypotheses) == attendus


# ── ÉTAPE 3 — fini_downward DÉRIVÉ (sous les 2 reports) ───────────────────────
def test_fini_downward_thm_conclusion_exacte():
    """⊢ (∀a)(∀x)fini_downward(a,x)   — EXACTEMENT l'unique hyp de N_collectivise()."""
    va, vx = var("a"), var("x")
    thm = C.fini_downward_thm("a", "x", "c", "b")
    cible = pourtout("a", pourtout("x", fini_downward(va, vx)))
    assert thm.conclusion == cible
    assert len(thm.hypotheses) == 2          # principe_recurrence + cardinal_pas_entre


def test_fini_downward_thm_reports_precis():
    """Les DEUX reports sont EXACTEMENT principe_recurrence(P) et (∀c)(∀b)cardinal_pas_entre."""
    vc, vb = var("c"), var("b")
    thm = C.fini_downward_thm("a", "x", "c", "b")
    P = C._P_pred("b")
    attendus = {
        C.principe_recurrence(P, "c"),
        pourtout("c", pourtout("b", C.cardinal_pas_entre(vb, vc))),
    }
    assert set(thm.hypotheses) == attendus


# ── ÉTAPE 4 — ℕ collectivisé, fini_downward DÉCHARGÉ ──────────────────────────
def test_N_collectivise_final_coll_sous_deux_reports():
    """⊢ coll(x, Fini x)  sous les SEULS reports principe_recurrence + cardinal_pas_entre.

    L'UNIQUE hypothèse fini_downward de N_collectivise() est DÉCHARGÉE par
    fini_downward_thm (ÉTAPE 3) ; il ne reste que les deux raccords structurels isolés.
    """
    thm = C.N_collectivise_final("a", "x", "c", "b")
    assert thm.conclusion == coll("x", est_fini(var("x")))
    assert len(thm.hypotheses) == 2
    # plus aucune hypothèse fini_downward « brute »
    va, vx = var("a"), var("x")
    B_brut = pourtout("a", pourtout("x", fini_downward(va, vx)))
    assert B_brut not in set(thm.hypotheses)


def test_N_collectivise_final_ne_postule_rien():
    """theorie_ensembles() = 22 : ni fini_downward, ni induction, ni collectivisation postulés."""
    C.N_collectivise_final("a", "x", "c", "b")
    assert len(E.theorie_ensembles().axiomes) == 22


# ── ÉTAPE 1 — énoncé reporté (cible structurelle) ─────────────────────────────
def test_cardinaux_bien_ordonnes_est_un_enonce():
    """cardinaux_bien_ordonnes(a) construit la FORMULE de bon ordre des cardinaux ≤ a.

    (∀S)( (S⊂[0,a] et S≠∅) ⇒ (∃m)(m∈S et (∀x)(x∈S ⇒ m ≤ x)) ).  REPORTÉ (ÉTAPE 1)."""
    f = C.cardinaux_bien_ordonnes("a")
    assert f.tag == "non"            # (∀S) = ¬(∃S)¬
    # forme attendue reconstruite indépendamment
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import inclus
    va, vS, vm, vx = var("a"), var("S"), var("m"), var("x")
    interv = E.intervalle_entiers(ZERO, va)
    hyp = et(inclus(vS, interv), non(egal(vS, E.VIDE)))
    pp = existe("m", et(appartient(vm, vS),
        pourtout("x", impl(appartient(vx, vS), inf_egal_card(vm, vx)))))
    assert f == pourtout("S", impl(hyp, pp))
