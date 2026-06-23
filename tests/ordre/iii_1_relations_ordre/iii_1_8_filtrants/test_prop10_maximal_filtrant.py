"""Tests — §III.1.10 Proposition 10 : maximal + filtrant à droite ⇒ plus grand.

Vérifie que le théorème `maximal_filtrant_est_plus_grand` est CERTIFIÉ par le
noyau (construction sans erreur), que sa conclusion est EXACTEMENT la cible
plus_grand_element(G,E,a), qu'il porte EXACTEMENT ses trois hypothèses HONNÊTES
(est_ordre, filtrant_droite_G, element_maximal ; jamais la conclusion parmi les
hypothèses → jamais vacuité), et que theorie_ensembles reste = 22 axiomes."""
from __future__ import annotations

import bourbaki.ordre.iii_1_relations_ordre.iii_1_8_filtrants.ensembles_prop10_maximal_filtrant as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, element_maximal,
)


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop10_conclusion_est_cible():
    t = M.maximal_filtrant_est_plus_grand()
    # conclusion EXACTEMENT plus_grand_element(G,E,a)
    assert t.conclusion == M._cible()


def test_prop10_trois_hypotheses_honnetes():
    t = M.maximal_filtrant_est_plus_grand()
    assert len(t.hypotheses) == 3          # est_ordre, filtrant_droite_G, element_maximal
    # jamais la conclusion en hypothèse (pas de vacuité)
    assert t.conclusion not in t.hypotheses
    # ensemble EXACT des trois hypothèses honnêtes
    honnetes = frozenset({
        est_ordre("Gmf", "Emf", "xmf", "ymf", "zmf"),
        M._filtrant_droite_G("Gmf", "Emf"),
        element_maximal("Gmf", "Emf", var("amf"), x="zpg10"),
    })
    assert t.hypotheses == honnetes
