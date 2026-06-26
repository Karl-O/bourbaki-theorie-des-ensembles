"""Tests — §III.1 n°12 REMARQUE (E.III.14) : un ensemble TOTALEMENT ordonné est
RÉTICULÉ.

Vérifie que le théorème `totalement_ordonne_implique_reticule` est CERTIFIÉ par le
noyau (construction sans erreur), que sa conclusion est EXACTEMENT `est_reticule(G,E)`
(reconstruit indépendamment du module via la définition du projet), qu'il porte
EXACTEMENT ses DEUX hypothèses HONNÊTES (est_ordre(G,E), totalite(G,E) ; jamais la
conclusion réticulé parmi les hypothèses → jamais vacuité), et que theorie_ensembles
reste = 22 axiomes."""
from __future__ import annotations

import bourbaki.ordre.iii_1_relations_ordre.iii_1_12_totalement_ordonnes.ensembles_total_implique_reticule as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import (
    var, et, ou, impl, appartient, pourtout,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, _couple_dans,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_monotone import (
    est_reticule,
)


_G, _E = "G", "E"


def _totalite_attendue():
    """Reconstruit totalite(G,E) À LA MAIN (mêmes constructeurs que l'énoncé), pour
    valider la fidélité INDÉPENDAMMENT du helper du module."""
    vx, vy, vE = var("x"), var("y"), var(_E)
    return pourtout("x", pourtout("y",
        impl(et(appartient(vx, vE), appartient(vy, vE)),
             ou(_couple_dans(vx, vy, _G), _couple_dans(vy, vx, _G)))))


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_total_reticule_se_construit():
    # le simple fait que la construction aboutisse = certification noyau
    t = M.totalement_ordonne_implique_reticule()
    assert t is not None


def test_total_reticule_conclusion_est_reticule():
    t = M.totalement_ordonne_implique_reticule()
    assert t.conclusion == M.cible_total_implique_reticule()     # cohérence interne (helper)
    assert t.conclusion == est_reticule(_G, _E)                  # fidélité (def du projet)


def test_total_reticule_deux_hypotheses_honnetes():
    t = M.totalement_ordonne_implique_reticule()
    # EXACTEMENT deux hypothèses honnêtes
    assert len(t.hypotheses) == 2
    # la conclusion réticulé n'est JAMAIS une hypothèse (pas de vacuité)
    assert t.conclusion not in t.hypotheses
    honnetes = frozenset({est_ordre(_G, _E), _totalite_attendue()})
    assert t.hypotheses == honnetes
    # cohérence avec le helper exposé par le module
    assert t.hypotheses == M.hypotheses_total_reticule()
    # la totalité reconstruite à la main == celle du module
    assert M.totalite(_G, _E) == _totalite_attendue()


def test_total_reticule_est_clos_sous_les_deux_hyps():
    t = M.totalement_ordonne_implique_reticule()
    # clos « modulo » les 2 hypothèses honnêtes : aucune hypothèse parasite
    honnetes = frozenset({est_ordre(_G, _E), _totalite_attendue()})
    assert t.hypotheses <= honnetes
