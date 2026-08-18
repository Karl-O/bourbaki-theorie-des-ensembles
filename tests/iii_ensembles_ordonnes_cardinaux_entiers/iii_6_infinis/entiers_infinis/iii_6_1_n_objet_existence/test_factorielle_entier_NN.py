# -*- coding: utf-8 -*-
"""Test §III.6.1 — le capstone ℕ : « n! est un entier » à 4 hypothèses.  theorie==22.

⚠️ TRÈS LENT (τ-lourd aux termes clos) : réservé aux lancements détachés."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_factorielle_entier_NN import (
    factorielle_entier_NN,
)
import pytest

#: FICHIER LOURD — 891 s mesurés le 18 août (pytest --durations).
#: Marqué slow : la porte « not slow » ne le voit plus, mais le théorème
#: reste vérifié par la suite COMPLÈTE — à lancer avant toute annonce.
pytestmark = pytest.mark.slow


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_factorielle_entier_NN():
    """🎯🎯🎯 3 hyps — les données de la règle SEULES —, conclusion ∀-close,
    theorie==22 après.  (La cible et chaque coupe sont assertées DANS le module.)"""
    th = factorielle_entier_NN()
    assert len(th.hypotheses) == 3
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
