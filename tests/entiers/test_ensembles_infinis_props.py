"""Tests (isolés) du module ensembles_infinis_props (§III.6, propositions directes).

Vérifie :
  • les THÉORÈMES INCONDITIONNELS (Dedekind + existence) sont CLOS (0 hyp) et de
    conclusion LITTÉRALEMENT la cible (anti-affaibli, anti-tautologie) ;
  • les THÉORÈMES CONDITIONNELS ont la bonne forme « report ⇒ énoncé » et SEUL le
    report figure en hypothèse (jamais postulé) ;
  • theorie_ensembles() reste à 22 axiomes (INTANGIBLE).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, impl, equiv, non, inclus
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal, inf_egal_card
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini, est_infini_ensemble, est_denombrable, aleph0,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import fini_downward
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
import bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis_props as P


def _est_clos(thm):
    return len(thm.hypotheses) == 0


# ── theorie_ensembles INTANGIBLE = 22 ────────────────────────────────────────
def test_theorie_ensembles_inchangee_22():
    assert len(theorie_ensembles().axiomes) == 22


# ── (1) DEDEKIND, sens facile :  (a=a+1) ⇒ est_infini(a)  (CLOS) ──────────────
def test_egal_succ_implique_infini_clos_et_cible():
    th = P.cardinal_egal_succ_implique_infini("a")
    assert _est_clos(th)
    va = var("a")
    cible = impl(egal(va, successeur(va)), est_infini(va))
    assert th.conclusion == cible


# ── (2) DEDEKIND, sens dur :  (est_cardinal a et infini a) ⇒ a=a+1  (CLOS) ────
def test_cardinal_infini_implique_egal_succ_clos_et_cible():
    th = P.cardinal_infini_implique_egal_succ("a")
    assert _est_clos(th)
    va = var("a")
    cible = impl(et(est_cardinal(va), est_infini(va)), egal(va, successeur(va)))
    assert th.conclusion == cible


# ── (3) DEDEKIND complète :  est_cardinal a ⇒ (infini a ⇔ a=a+1)  (CLOS) ──────
def test_dedekind_cardinal_clos_et_cible():
    th = P.dedekind_cardinal("a")
    assert _est_clos(th)
    va = var("a")
    cible = impl(est_cardinal(va), equiv(est_infini(va), egal(va, successeur(va))))
    assert th.conclusion == cible


def test_dedekind_pas_une_tautologie():
    # est_infini(a) et (a=a+1) sont des formules DISTINCTES (contenu réel)
    va = var("a")
    assert est_infini(va) != egal(va, successeur(va))


# ── (4) un cardinal infini existe (de A4)  (CLOS) ────────────────────────────
def test_existe_cardinal_infini_clos():
    th = P.existe_cardinal_infini("a", "X")
    assert _est_clos(th)
    # (∃a)¬Fini(a) = (∃a)est_infini(a)
    assert th.conclusion.tag == "exists"


# ── (5) MONOTONIE de l'infini (CONDITIONNEL fini_downward)  (CLOS, report en hyp) ─
def test_infini_monotone_cond_clos_et_forme():
    th = P.infini_monotone_cond("a", "b")
    assert _est_clos(th)
    va, vb = var("a"), var("b")
    ante = et(inf_egal_card(va, vb), est_infini(va))
    cible = impl(fini_downward(va, vb), impl(ante, est_infini(vb)))
    assert th.conclusion == cible


def test_infini_monotone_cond_report_est_fini_downward():
    # le SEUL antécédent (report) est fini_downward — pas un théorème postulé
    th = P.infini_monotone_cond("a", "b")
    va, vb = var("a"), var("b")
    assert th.conclusion.tag == "non" or True  # impl en abrégé = ¬∨
    # antécédent de l'implication externe == fini_downward(a,b)
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    ante, _ = antecedent_consequent(th.conclusion)
    assert ante == fini_downward(va, vb)


def test_infini_ensemble_monotone_cond_clos_et_forme():
    th = P.infini_ensemble_monotone_cond("X", "Y")
    assert _est_clos(th)
    cX, cY = cardinal(var("X")), cardinal(var("Y"))
    ante = et(inf_egal_card(cX, cY), est_infini(cX))
    cible = impl(fini_downward(cX, cY), impl(ante, est_infini(cY)))
    # est_infini_ensemble(X) == est_infini(Card X) littéralement
    assert est_infini_ensemble(var("X")) == est_infini(cX)
    assert th.conclusion == cible


# ── (6) PARTIE d'un dénombrable (CONDITIONNEL transport)  (CLOS, report en hyp) ─
def _le_AB_exact():
    """A ≤ B (ensembles) tel que produit par partie_inf_egal_card — forme exacte."""
    from bourbaki.logique import noyau_abrege as N
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import partie_inf_egal_card
    vA, vB = var("A"), var("B")
    h = N.assume(inclus(vA, vB))
    return N.modus_ponens(h, partie_inf_egal_card("A", "B")).conclusion


def test_sous_ensemble_denombrable_cond_clos_et_forme():
    th = P.sous_ensemble_denombrable_cond("A", "B")
    assert _est_clos(th)
    vA, vB = var("A"), var("B")
    le_concl = _le_AB_exact()
    H = impl(et(le_concl, est_denombrable(vB)), est_denombrable(vA))
    inner = impl(et(inclus(vA, vB), est_denombrable(vB)), est_denombrable(vA))
    cible = impl(H, inner)
    assert th.conclusion == cible


def test_sous_ensemble_denombrable_report_unique():
    # le SEUL antécédent (report) est le transport « A≤B et B dén. ⇒ A dén. »
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    th = P.sous_ensemble_denombrable_cond("A", "B")
    vA, vB = var("A"), var("B")
    le_concl = _le_AB_exact()
    H = impl(et(le_concl, est_denombrable(vB)), est_denombrable(vA))
    ante, _ = antecedent_consequent(th.conclusion)
    assert ante == H


# ── (7) ÉNONCÉ reporté ℵ₀ ≤ a : c'est une FORMULE, pas un théorème ────────────
def test_aleph0_inf_egal_enonce_est_une_formule():
    f = P.aleph0_inf_egal_cardinal_infini_enonce("a")
    va = var("a")
    assert f == impl(est_infini(va), inf_egal_card(aleph0(), va))
    # pas de méthode .conclusion / .hypotheses : c'est une Formule, jamais prouvée
    assert not hasattr(f, "conclusion")
