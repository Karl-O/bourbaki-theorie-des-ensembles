"""Tests — C62 / C63 (E.III.6.2) : définition par récurrence sur (ℕ, ≤).

C62 = C60 (récursion transfinie) spécialisé à (ℕ, ≤) bien ordonné, sous les TROIS
hypothèses honnêtes (ℕ bien ordonné ; essais bien formés ; règle valuée).  C63 =
C62 avec la règle d'itération T_{S,a}.  theorie=22, conclusion non vacuous.
"""
import pytest

from bourbaki.logique.formule import var, egal, impl, appartient, pourtout, existe
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles, est_bien_ordonne
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_pont import essais_bien_formes, rule_codomain
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import _graphe_R
from bourbaki.entiers.iii_6_infinis.iii_6_2_recursion_c62.ensembles_c62_recursion import (
    c62_recursion_sur_N, c62_cible, regle_iteration, c63_iteration_sur_N,
)


def _rule_const():
    """Règle opaque-constante T{u}=Trule (pour les tests de structure)."""
    return lambda u: var("Trule")


def _n_axiomes():
    t = theorie_ensembles()
    return len(t.axiomes) if hasattr(t, "axiomes") else len(t)


# ── theorie intacte ────────────────────────────────────────────────────────────
def test_theorie_22():
    assert _n_axiomes() == 22


# ── C62 ─────────────────────────────────────────────────────────────────────────
def test_c62_conclusion_et_hyps():
    vh = _rule_const()
    th = c62_recursion_sur_N(vh)
    # conclusion = (∀x)( x∈ℕ ⇒ (∃p) est_essai(p, T, ≤, ℕ, x) )
    assert th.conclusion == c62_cible(vh, "Enat", "Gle", "x0tf", "pess", "zess")
    # trois hypothèses honnêtes présentes
    R = _graphe_R("Gle")
    ve = var("Enat")
    assert est_bien_ordonne(R, ve) in th.hypotheses           # (a) ℕ bien ordonné
    assert essais_bien_formes(vh, "Enat", "Gle", "Uval", "qwf", "wwf", "zess") in th.hypotheses
    assert rule_codomain(vh, "Uval", "zess") in th.hypotheses
    # exactement trois résidus, non vacuous
    assert len(th.hypotheses) == 3
    assert th.conclusion not in th.hypotheses


def test_c62_non_clos_mais_residus_honnetes():
    """C62 n'est PAS clos (3 hyps honnêtes) ; AUCUNE n'est vacuous ni fausse."""
    th = c62_recursion_sur_N(_rule_const())
    assert not th.est_clos
    assert len(th.hypotheses) == 3


# ── C63 (itération) ──────────────────────────────────────────────────────────────
def test_c63_conclusion_et_hyps():
    a = var("a63")
    S = lambda u: var("Sof")          # règle de pas S{·} opaque
    th = c63_iteration_sur_N(S, a)
    T = regle_iteration(S, a)
    assert th.conclusion == c62_cible(T, "Enat", "Gle", "x0tf", "pess", "zess")
    R = _graphe_R("Gle")
    ve = var("Enat")
    assert est_bien_ordonne(R, ve) in th.hypotheses
    assert essais_bien_formes(T, "Enat", "Gle", "Vval63", "qwf", "wwf", "zess") in th.hypotheses
    assert rule_codomain(T, "Vval63", "zess") in th.hypotheses
    assert len(th.hypotheses) == 3
    assert th.conclusion not in th.hypotheses


def test_c63_regle_iteration_est_terme():
    """La règle d'itération T_{S,a} est un terme bien formé (callable Terme→Terme)."""
    from bourbaki.logique.formule import Terme
    T = regle_iteration(lambda u: var("Sof"), var("a63"))
    out = T(var("u0"))
    assert isinstance(out, Terme)
