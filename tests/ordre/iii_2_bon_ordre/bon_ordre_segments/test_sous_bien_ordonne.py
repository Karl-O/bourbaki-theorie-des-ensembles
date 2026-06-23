"""Tests — Chapitre III §2 : une partie d'un ensemble bien ordonné est bien ordonnée.

On vérifie le théorème `sous_ensemble_bien_ordonne` sur sa CIBLE EXACTE :
  { est_bien_ordonne(R, E),  inclus(S, E) }  ⊢  est_bien_ordonne(R_S, S)
avec R_S = ordre_induit(R, S) (ordre induit par R sur S).  On contrôle aussi la
non-vacuité, les hypothèses exactes, et l'invariant theorie_ensembles = 22 axiomes.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, appartient, inclus
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_2_bon_ordre.bon_ordre_segments import ensembles_sous_bien_ordonne as SBO


def _R(a, b):
    """Relation-test R{x,y} := (x,y)∈G (un graphe G fixé), R notée ≤."""
    return appartient(E.couple(a, b), var("G"))


def test_sous_ensemble_bien_ordonne_cible():
    th = SBO.sous_ensemble_bien_ordonne(_R)
    ve, vS = var("E"), var("S")
    RS = E.ordre_induit(_R, vS)
    cible = E.est_bien_ordonne(RS, vS)
    # conclusion = est_bien_ordonne(R_S, S)
    assert th.conclusion == cible


def test_sous_ensemble_bien_ordonne_hypotheses():
    th = SBO.sous_ensemble_bien_ordonne(_R)
    ve, vS = var("E"), var("S")
    hyp_bo = E.est_bien_ordonne(_R, ve)         # E bien ordonné par R
    hyp_inc = inclus(vS, ve)                    # S ⊂ E
    # EXACTEMENT les deux hypothèses voulues, rien de plus.
    assert th.hypotheses == frozenset({hyp_bo, hyp_inc})


def test_sous_ensemble_bien_ordonne_non_vacuous():
    th = SBO.sous_ensemble_bien_ordonne(_R)
    # non vacuité : la conclusion n'est pas l'une des hypothèses (pas de P⇒P).
    assert th.conclusion not in th.hypotheses


def test_theorie_ensembles_invariante():
    # le cœur du projet : theorie_ensembles reste EXACTEMENT 22 axiomes.
    assert len(E.theorie_ensembles().axiomes) == 22
