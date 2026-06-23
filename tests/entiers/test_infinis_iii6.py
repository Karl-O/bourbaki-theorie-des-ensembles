"""Tests §III.6 — ℵ₀ EST UN CARDINAL INFINI : conséquences CLOSES de ℵ₀ = ℵ₀+1.

Tous les théorèmes de ensembles_infinis_iii6.py sont CLOS (est_clos, 0 hyp, theorie=22)
et NON vacuous (conclusion ≠ une hypothèse).  Travaillent sur le ℵ₀ CONCRET
ℵ₀ = Card(ensemble_NN()), pour lequel l'équation ℵ₀ = ℵ₀+1 est prouvée (aleph0_egal_succ).

  RAPIDES (n'invoquent pas aleph0_egal_succ / N_existe) :
    • aleph0_est_cardinal        ⊢ est_cardinal(ℵ₀)
    • aleph0_inf_egal_reflexif   ⊢ ℵ₀ ≤ ℵ₀          (ℕ dénombrable, sens cardinal)
    • NN_denombrable             ⊢ (∃Y)(Y⊂ℕ et Eq(ℕ,Y))   (Déf. 3)

  LENTS (via aleph0_egal_succ / aleph0_infini — mémoïsés, regroupés, @slow) :
    • aleph0_plus_un_egal        ⊢ ℵ₀+1 = ℵ₀
    • aleph0_est_infini          ⊢ est_infini(ℵ₀)
    • NN_est_infini_ensemble     ⊢ est_infini_ensemble(ℕ)
    • dedekind_aleph0            ⊢ est_infini(ℵ₀) ⇔ (ℵ₀=ℵ₀+1)
    • existe_cardinal_infini_concret ⊢ (∃a) est_infini(a)   (A4 réalisé par ℵ₀)
"""
import pytest

from bourbaki.logique.i_1_termes_relations.formule import var, egal, equiv, existe, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card, equipotent, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import aleph_0
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini, est_infini_ensemble

from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis_iii6 import (
    aleph0_est_cardinal, aleph0_inf_egal_reflexif, NN_denombrable,
    aleph0_plus_un_egal, aleph0_est_infini, NN_est_infini_ensemble,
    dedekind_aleph0, existe_cardinal_infini_concret,
    aleph0_strict_continu_concret, continu_non_denombrable_concret,
)
from bourbaki.cardinaux.ensembles_cardinaux import inf_strict_card


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── RAPIDES ───────────────────────────────────────────────────────────────────
def test_aleph0_est_cardinal():
    th = aleph0_est_cardinal()
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == est_cardinal(aleph_0())
    assert th.conclusion.tag == "exists"               # non-vacuous : (∃X)(ℵ₀=Card X)


def test_aleph0_inf_egal_reflexif():
    th = aleph0_inf_egal_reflexif()
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == inf_egal_card(aleph_0(), aleph_0())


def test_NN_denombrable():
    th = NN_denombrable()
    assert th.est_clos and not th.hypotheses
    NN = ensemble_NN()
    corps = E.et(inclus(var("Y"), NN), equipotent(NN, var("Y")))
    assert th.conclusion == existe("Y", corps)         # Déf. 3, témoin Y=ℕ
    assert th.conclusion.tag == "exists"


def test_aleph0_strict_continu_concret():
    th = aleph0_strict_continu_concret()
    assert th.est_clos and not th.hypotheses
    NN = ensemble_NN()
    assert th.conclusion == inf_strict_card(cardinal(NN), cardinal(E.parties(NN)))


def test_continu_non_denombrable_concret():
    th = continu_non_denombrable_concret()
    assert th.est_clos and not th.hypotheses
    NN = ensemble_NN()
    assert th.conclusion == E.non(inf_egal_card(cardinal(E.parties(NN)), cardinal(NN)))
    assert th.conclusion.tag == "non"


# ── LENTS (aleph0_egal_succ / aleph0_infini, mémoïsés) ─────────────────────────
@pytest.mark.slow
def test_aleph0_infini_consequences():
    """🎯 Conséquences §III.6 de ℵ₀ = ℵ₀+1 — toutes CLOSES, 0 hyp, theorie=22, non-vacuous."""
    a0 = aleph_0()
    NN = ensemble_NN()

    plus_un = aleph0_plus_un_egal()
    assert plus_un.est_clos and not plus_un.hypotheses
    assert plus_un.conclusion == egal(successeur(a0), a0)    # ℵ₀+1 = ℵ₀

    inf = aleph0_est_infini()
    assert inf.est_clos and not inf.hypotheses
    assert inf.conclusion == est_infini(a0)                  # = ¬Fini(ℵ₀)
    assert inf.conclusion.tag == "non"

    inf_ens = NN_est_infini_ensemble()
    assert inf_ens.est_clos and not inf_ens.hypotheses
    assert inf_ens.conclusion == est_infini_ensemble(NN)

    ded = dedekind_aleph0()
    assert ded.est_clos and not ded.hypotheses
    assert ded.conclusion == equiv(est_infini(a0), egal(a0, successeur(a0)))

    ex = existe_cardinal_infini_concret()
    assert ex.est_clos and not ex.hypotheses
    assert ex.conclusion == existe("a", est_infini(var("a")))
    assert ex.conclusion.tag == "exists"

    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_22_apres():
    assert len(E.theorie_ensembles().axiomes) == 22
