"""Tests — §III.1.11 Remarque (E.III.13) : réticulé ⇒ filtrant à droite ET à gauche.

Vérifie que le théorème `reticule_implique_filtrant_droite_gauche` est CERTIFIÉ
par le noyau (construction sans erreur), que sa conclusion est EXACTEMENT la cible
(filtrant_droite_G et filtrant_gauche_G), qu'il porte EXACTEMENT son unique
hypothèse HONNÊTE est_reticule(G,E) (jamais la conclusion parmi les hypothèses →
jamais vacuité), et que theorie_ensembles reste = 22 axiomes."""
from __future__ import annotations

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.iii_1_11_reticules.ensembles_reticule_filtrant as M
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_remarque_conclusion_est_cible():
    t = M.reticule_implique_filtrant_droite_gauche()
    # conclusion EXACTEMENT (filtrant_droite_G(G,E) et filtrant_gauche_G(G,E))
    assert t.conclusion == M.cible_reticule_implique_filtrant()


def test_remarque_unique_hypothese_honnete():
    t = M.reticule_implique_filtrant_droite_gauche()
    # une SEULE hypothèse honnête : est_reticule(G,E)
    assert len(t.hypotheses) == 1
    # jamais la conclusion en hypothèse (pas de vacuité)
    assert t.conclusion not in t.hypotheses
    # ensemble EXACT de l'unique hypothèse honnête
    assert t.hypotheses == frozenset({M.hypothese_reticule()})


def test_remarque_clos_au_sens_du_projet():
    # « clos au sens du projet » = aucune hypothèse HORS l'énoncé : ici l'unique
    # hypothèse est exactement la prémisse est_reticule(G,E) de la Remarque.
    t = M.reticule_implique_filtrant_droite_gauche()
    assert t.hypotheses - {M.hypothese_reticule()} == frozenset()
