"""Tests — §III.1 Proposition 4 (E.III.9) : A≠∅ ⇒ inf A ≤ sup A.

Vérifie que le théorème est CERTIFIÉ par le noyau (construction sans erreur), que
sa conclusion est EXACTEMENT la cible (i,s)∈G, qu'il porte EXACTEMENT ses quatre
hypothèses HONNÊTES (transitivité, A≠∅, inf, sup ; jamais la conclusion parmi les
hypothèses → jamais vacuité), et que theorie_ensembles reste = 22 axiomes."""
from __future__ import annotations

import bourbaki.ordre.iii_1_relations_ordre.bornes_sup.ensembles_inf_sup_prop4_iii1 as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var, existe, appartient
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    transitivite_rel, borne_inferieure, borne_superieure,
)


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop4_conclusion_est_cible():
    t = M.inf_le_sup()
    # conclusion EXACTEMENT (i,s)∈G
    assert t.conclusion == M._cible()


def test_prop4_quatre_hypotheses_honnetes():
    t = M.inf_le_sup()
    assert len(t.hypotheses) == 4          # transitivité, A≠∅, inf, sup
    # jamais la conclusion en hypothèse (pas de vacuité)
    assert t.conclusion not in t.hypotheses
    # ensemble EXACT des quatre hypothèses honnêtes
    honnetes = frozenset({
        transitivite_rel("G", "x", "y", "t"),
        existe("a", appartient(var("a"), var("A"))),          # A ≠ ∅ : (∃a)(a∈A)
        borne_inferieure("G", "A", var("i"), "E", "x", "y"),  # i = inf A
        borne_superieure("G", "A", var("s"), "E", "x", "y"),  # s = sup A
    })
    assert t.hypotheses == honnetes
