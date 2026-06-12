"""Tests (isolés) du module ensembles_chap3_props_restantes (§III — Cantor cardinal).

Vérifie :
  • chaque THÉORÈME est CLOS (0 hypothèse) ;
  • sa conclusion est LITTÉRALEMENT la cible attendue (anti-affaibli, anti-tautologie) ;
  • theorie_ensembles() reste à 22 axiomes (INTANGIBLE) ;
  • le LEMME est_cardinal_de_cardinal est polymorphe (str ET Terme) ;
  • cantor_strict_cardinal / cantor_deux_exp sont génériques (X quelconque).
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, non
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card, inf_strict_card, est_cardinal,
)
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire
from bourbaki.cardinaux.arithmetique.ensembles_powerset_exp import deux
from bourbaki.entiers.ensembles_infinis import NN, aleph0, puissance_continu, est_denombrable_card
import bourbaki.entiers.ensembles_chap3_props_restantes as P


def _est_clos(thm):
    return len(thm.hypotheses) == 0


# ── theorie_ensembles INTANGIBLE = 22 ────────────────────────────────────────
def test_theorie_ensembles_inchangee_22():
    assert len(theorie_ensembles().axiomes) == 22


# ── LEMME : est_cardinal(Card X) (str et Terme) ──────────────────────────────
def test_est_cardinal_de_cardinal_clos_et_cible():
    th = P.est_cardinal_de_cardinal("X")
    assert _est_clos(th)
    assert th.conclusion == est_cardinal(cardinal(var("X")))


def test_est_cardinal_de_cardinal_terme():
    th = P.est_cardinal_de_cardinal(NN)
    assert _est_clos(th)
    assert th.conclusion == est_cardinal(cardinal(NN))


# ── (1) CANTOR au niveau CARDINAL : Card X < Card P(X) ───────────────────────
def test_cantor_strict_cardinal_clos_et_cible():
    th = P.cantor_strict_cardinal("X")
    assert _est_clos(th)
    vX = var("X")
    assert th.conclusion == inf_strict_card(cardinal(vX), cardinal(E.parties(vX)))


def test_cantor_strict_cardinal_generique():
    # générique : d'autres noms de variable (str ET Terme-variable) ; NN couvert ailleurs
    for x in ["A", var("Q")]:
        th = P.cantor_strict_cardinal(x)
        assert _est_clos(th)
        vX = x if not isinstance(x, str) else var(x)
        assert th.conclusion == inf_strict_card(cardinal(vX), cardinal(E.parties(vX)))


# ── (2) THÉORÈME 2 de Cantor restaté : Card X < 2^Card X ─────────────────────
def test_cantor_deux_exp_clos_et_cible():
    th = P.cantor_deux_exp("X")
    assert _est_clos(th)
    vX = var("X")
    cible = inf_strict_card(cardinal(vX), exposant_cardinal_binaire(deux(), vX))
    assert th.conclusion == cible


# ── (3) ℵ₀ < 2^ℵ₀  et  ℵ₀ ≤ 2^ℵ₀ ────────────────────────────────────────────
def test_aleph0_strict_continu_clos_et_cible():
    th = P.aleph0_strict_continu()
    assert _est_clos(th)
    # ℵ₀ = Card N, 2^ℵ₀ = Card P(N) = puissance_continu()
    assert th.conclusion == inf_strict_card(aleph0(), puissance_continu())


def test_aleph0_inf_egal_continu_clos_et_cible():
    th = P.aleph0_inf_egal_continu()
    assert _est_clos(th)
    assert th.conclusion == inf_egal_card(aleph0(), puissance_continu())


# ── (4) la puissance du continu n'est PAS ≤ ℵ₀ (P(N) non dénombrable) ────────
def test_continu_non_denombrable_card_clos_et_cible():
    th = P.continu_non_denombrable_card()
    assert _est_clos(th)
    # ¬( 2^ℵ₀ ≤ ℵ₀ ) = ¬( Card P(N) ≤ Card N )
    assert th.conclusion == non(inf_egal_card(puissance_continu(), aleph0()))


def test_continu_non_denombrable_est_negation_de_denombrable_card():
    # est_denombrable_card(P N) = (Card P(N) ≤ ℵ₀) ; notre théorème en est la négation
    th = P.continu_non_denombrable_card()
    assert th.conclusion == non(est_denombrable_card(E.parties(NN)))
