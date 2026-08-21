# -*- coding: utf-8 -*-
"""Tests §III.6 (prérequis Lemme 2) — arithmétique multiplicative vers le couplage 2^m·3^n.

Miroir de ensembles_denombrable_injection_iii6 (module SANS test jusqu'ici —
dette découverte le 22 août) : les 5 lemmes, chacun contre sa cible, 0 hyp,
theorie=22.
"""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_injection_iii6 import (
    puissance_succ_eq_incond, puissance_succ_eq_incond_cible,
    trois_impair,
    trois_puiss_impair, trois_puiss_impair_cible,
    deux_puiss_pair, deux_puiss_pair_cible,
    simplification_multiplicative, simplification_multiplicative_cible,
)


def test_puissance_succ_eq_incond():
    """⊢ (card a et Fini n) ⇒ a^(n+1) = a^n·a, inconditionnel."""
    r = puissance_succ_eq_incond()
    assert not r.hypotheses
    assert r.conclusion == puissance_succ_eq_incond_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_trois_impair():
    """⊢ ¬(2 | 3)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
        est_impair_propre)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
        TROIS)
    r = trois_impair()
    assert not r.hypotheses
    assert r.conclusion == est_impair_propre(TROIS)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_trois_puiss_impair():
    """⊢ Fini n ⇒ ¬(2 | 3^n)   (récurrence C61)."""
    r = trois_puiss_impair()
    assert not r.hypotheses
    assert r.conclusion == trois_puiss_impair_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_deux_puiss_pair():
    """⊢ (Fini k et k≠0) ⇒ (2 | 2^k)."""
    r = deux_puiss_pair()
    assert not r.hypotheses
    assert r.conclusion == deux_puiss_pair_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_simplification_multiplicative():
    """⊢ (entiers, c≠0, a·c=b·c) ⇒ a=b   (cancellation N)."""
    r = simplification_multiplicative()
    assert not r.hypotheses
    assert r.conclusion == simplification_multiplicative_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
