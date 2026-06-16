"""Tests §III.6 — ℵ₀ = Card(NN), route Cantor-Bernstein vers ℵ₀ = ℵ₀+1.

CLOS (vérifiés est_clos, 0 hyp, conclusion exacte, non-vacuous, theorie=22) :
  • successeur_non_nul   ⊢ ¬(successeur(t)=0)            (NN-indépendant) ;
  • inf_egal_NN_diff     ⊢ inf_egal_card(NN∖{0}, NN)     (NN-indépendant, moitié facile).

⚠ La moitié DURE inf_egal_NN (NN ≤ NN∖{0}, via la translation injective n↦succ(n))
RESTE OUVERTE : verrou structurel de binders (voir docstring du module).  Les
théorèmes en aval (NN_eq_NN_sans_zero, aleph0_egal_succ, aleph0_infini) en dépendent
et ne sont donc pas encore clos.
"""
import pytest

from bourbaki.logique.formule import var, egal, non
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.entiers.ensembles_entiers import successeur, ZERO
from bourbaki.entiers.ensembles_ensemble_NN import ensemble_NN
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.entiers.ensembles_aleph0 import (
    successeur_non_nul, inf_egal_NN_diff, _NN_sans_zero, s_injective_safe, _s,
)
from bourbaki.entiers.ensembles_ensemble_NN import ensemble_NN as _NN


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_successeur_non_nul():
    th = successeur_non_nul()                  # binder défaut « j »
    assert th.est_clos
    assert not th.hypotheses
    assert th.conclusion == non(egal(successeur(var("j")), ZERO))
    # non-vacuous : la conclusion est une négation d'égalité concrète (non triviale)
    assert th.conclusion.tag == "non"


def test_inf_egal_NN_diff():
    th = inf_egal_NN_diff()
    assert th.est_clos
    assert not th.hypotheses
    assert th.conclusion == inf_egal_card(_NN_sans_zero(), ensemble_NN())
    # non-vacuous : c'est bien un ∃F (encodé ¬∀¬), pas une tautologie
    assert th.conclusion.tag in ("non", "exists")


def test_s_injective_safe():
    """MATH de l'injectivité de la translation (étape 3) — CLOSE en liants SÛRS m0/m0p.

    ⚠ Lent (Prop 8 + N_existe).  Non convertible vers la forme défaut u/up exigée par
    est_injection_de (verrou structurel de liants, cf. docstring du module)."""
    inj = s_injective_safe()
    assert inj.est_clos
    assert not inj.hypotheses
    assert inj.conclusion == E.injective_dans(_s(_NN()), _NN(), "m0", "m0p")


def test_theorie_22_apres():
    # invariant intact après construction des théorèmes
    assert len(E.theorie_ensembles().axiomes) == 22
