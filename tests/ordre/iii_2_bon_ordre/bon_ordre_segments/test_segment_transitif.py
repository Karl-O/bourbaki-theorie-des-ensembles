"""Tests — Chapitre III §2 : transitivité des segments (E.III.2.1, Définition 2).

On vérifie le théorème `segment_de_segment_est_segment` sur sa CIBLE EXACTE :
  { est_segment(S,R,E), est_segment(T,R,S) }  ⊢  est_segment(T,R,E)
On contrôle la conclusion, les hypothèses EXACTES, la non-vacuité, et l'invariant
theorie_ensembles = 22 axiomes.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_2_bon_ordre.bon_ordre_segments import ensembles_segment_transitif as ST


def _R(a, b):
    """Relation-test R{x,y} := (x,y)∈G (un graphe G fixé), R notée ≤."""
    return appartient(E.couple(a, b), var("G"))


def test_segment_de_segment_cible():
    th = ST.segment_de_segment_est_segment(_R)
    vS, vT, ve = var("S"), var("T"), var("E")
    cible = E.est_segment(vT, _R, ve)               # est_segment(T,R,E)
    assert th.conclusion == cible


def test_segment_de_segment_hypotheses():
    th = ST.segment_de_segment_est_segment(_R)
    vS, vT, ve = var("S"), var("T"), var("E")
    hyp_S = E.est_segment(vS, _R, ve)               # S segment de E
    hyp_T = E.est_segment(vT, _R, vS)               # T segment de S
    # EXACTEMENT les deux hypothèses voulues, rien de plus.
    assert th.hypotheses == frozenset({hyp_S, hyp_T})


def test_segment_de_segment_non_vacuous():
    th = ST.segment_de_segment_est_segment(_R)
    # non vacuité : la conclusion n'est pas l'une des hypothèses (pas de P⇒P).
    assert th.conclusion not in th.hypotheses


def test_theorie_ensembles_invariante():
    # le cœur du projet : theorie_ensembles reste EXACTEMENT 22 axiomes.
    assert len(E.theorie_ensembles().axiomes) == 22
