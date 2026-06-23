"""Tests — §III.2.1 : le segment du PLUS PETIT élément est vide.

On vérifie le théorème `segment_du_plus_petit_est_vide` sur sa CIBLE EXACTE :

  { est_bien_ordonne(R,E),  est_plus_petit_element(R,E,α) }  ⊢  seg(R,E,α) = ∅.

Pour le résultat : conclusion == cible, hypothèses EXACTES (les deux antécédents
load-bearing), non-vacuité, et l'invariant theorie_ensembles = 22 axiomes.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_2_bon_ordre.bon_ordre_segments import (
    ensembles_segment_minimum as SM,
)


def _Rgraphe(a, b):
    """Relation-test R{a,b} := (a,b)∈R (même lecture que seg/membre_segment)."""
    return appartient(E.couple(a, b), var("R"))


def test_segment_minimum_cible():
    th = SM.segment_du_plus_petit_est_vide()
    cible = SM.segment_du_plus_petit_est_vide_cible()       # seg(R,E,α)=∅
    assert th.conclusion == cible


def test_segment_minimum_hypotheses():
    th = SM.segment_du_plus_petit_est_vide()
    ve, va = var("E"), var("alpha")
    h_bo = E.est_bien_ordonne(_Rgraphe, ve)                 # E bien ordonné
    h_pp = E.est_plus_petit_element(_Rgraphe, ve, va)       # α plus petit de E
    # EXACTEMENT les deux antécédents voulus, rien de plus.
    assert th.hypotheses == frozenset({h_bo, h_pp})


def test_segment_minimum_non_vacuous():
    th = SM.segment_du_plus_petit_est_vide()
    # non vacuité : la conclusion n'est pas l'une des hypothèses (pas de P⇒P).
    assert th.conclusion not in th.hypotheses


def test_theorie_ensembles_invariante():
    # le cœur du projet : theorie_ensembles reste EXACTEMENT 22 axiomes.
    assert len(E.theorie_ensembles().axiomes) == 22
