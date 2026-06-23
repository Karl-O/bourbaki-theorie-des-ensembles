"""Tests miroir de ensembles_cardinaux_consequences (§III.3, conséquences de l'ordre).

On vérifie :
  • la CLÔTURE (est_clos) des théorèmes inconditionnels (0 hypothèse) ;
  • la CONCLUSION LITTÉRALE de chacun (anti-tautologie / anti-affaibli) ;
  • pour les conditionnels, que l'hypothèse est BIEN celle annoncée (et non vide) ;
  • theorie_ensembles() reste = 22.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, et, ou, non, existe
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal, cardinal)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN
from bourbaki.cardinaux.ensembles_cardinaux_consequences import (
    strict_implique_inf_egal, strict_irreflexif,
    cantor_strict_existe, aucun_plus_grand_cardinal,
    inf_egal_strict_compose, strict_inf_egal_compose, strict_transitive,
    un_inf_egal_exposant_conditionnel, base_inf_egal_exposant_conditionnel,
)


def test_theorie_intangible():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── (A) a < b ⇒ a ≤ b ──────────────────────────────────────────────────────────
def test_strict_implique_inf_egal_conclusion():
    from bourbaki.logique.formule import impl
    thm = strict_implique_inf_egal("a", "b")
    assert thm.est_clos
    va, vb = var("a"), var("b")
    assert thm.conclusion == impl(inf_strict_card(va, vb), inf_egal_card(va, vb))


# ── (B) ¬(a < a) ────────────────────────────────────────────────────────────────
def test_strict_irreflexif_clos():
    thm = strict_irreflexif("a")
    assert thm.est_clos
    va = var("a")
    assert thm.conclusion == non(inf_strict_card(va, va))


# ── (C) pas de plus grand cardinal ──────────────────────────────────────────────
def test_cantor_strict_existe_clos():
    thm = cantor_strict_existe("X")
    assert thm.est_clos
    vX = var("X")
    assert thm.conclusion == existe("Y", inf_strict_card(vX, var("Y")))


def test_aucun_plus_grand_cardinal_clos():
    thm = aucun_plus_grand_cardinal("X")
    assert thm.est_clos
    # (∀X)(∃Y)(X<Y)  : forme ¬∃¬ pour pourtout
    assert thm.conclusion.tag == "non"  # (∀X) = ¬(∃X)¬


# ── (D) transitivité stricte (gardée cardinaux) ─────────────────────────────────
def _build_hyp_inf_strict(va, vb, vc):
    h = et(et(et(inf_egal_card(va, vb), inf_strict_card(vb, vc)),
              est_cardinal(va)), est_cardinal(vb))
    return et(h, est_cardinal(vc))


def test_inf_egal_strict_compose_clos_et_conclusion():
    from bourbaki.logique.formule import impl
    thm = inf_egal_strict_compose("a", "b", "c")
    assert thm.est_clos
    va, vb, vc = var("a"), var("b"), var("c")
    hyp = _build_hyp_inf_strict(va, vb, vc)
    assert thm.conclusion == impl(hyp, inf_strict_card(va, vc))


def test_strict_inf_egal_compose_clos_et_conclusion():
    from bourbaki.logique.formule import impl
    thm = strict_inf_egal_compose("a", "b", "c")
    assert thm.est_clos
    va, vb, vc = var("a"), var("b"), var("c")
    h = et(et(et(inf_strict_card(va, vb), inf_egal_card(vb, vc)),
              est_cardinal(va)), est_cardinal(vb))
    hyp = et(h, est_cardinal(vc))
    assert thm.conclusion == impl(hyp, inf_strict_card(va, vc))


def test_strict_transitive_clos_et_conclusion():
    from bourbaki.logique.formule import impl
    thm = strict_transitive("a", "b", "c")
    assert thm.est_clos
    va, vb, vc = var("a"), var("b"), var("c")
    h = et(et(et(inf_strict_card(va, vb), inf_strict_card(vb, vc)),
              est_cardinal(va)), est_cardinal(vb))
    hyp = et(h, est_cardinal(vc))
    assert thm.conclusion == impl(hyp, inf_strict_card(va, vc))
    # anti-tautologie : conclusion ≠ hypothèse
    assert hyp != inf_strict_card(va, vc)


# ── (E) bornes exponentielles conditionnelles ──────────────────────────────────
def test_un_inf_egal_exposant_conditionnel():
    from bourbaki.logique.formule import impl
    thm = un_inf_egal_exposant_conditionnel("a", "b")
    assert thm.est_clos
    va, vb = var("a"), var("b")
    Fba = E.applications(vb, va)
    hyp = inf_egal_card(UN, Fba)
    concl = inf_egal_card(cardinal(UN), cardinal(Fba))
    assert thm.conclusion == impl(hyp, concl)
    # NON tautologique : hyp ≠ conclusion
    assert hyp != concl


def test_base_inf_egal_exposant_conditionnel():
    from bourbaki.logique.formule import impl
    thm = base_inf_egal_exposant_conditionnel("a", "b")
    assert thm.est_clos
    va, vb = var("a"), var("b")
    Fba = E.applications(vb, va)
    hyp = inf_egal_card(va, Fba)
    concl = inf_egal_card(cardinal(va), cardinal(Fba))
    assert thm.conclusion == impl(hyp, concl)
    assert hyp != concl
