# -*- coding: utf-8 -*-
"""Test §III.5.6 Déf. 1 — reste, quotient, multiple, divisible, diviseur (défs fidèles).

Constructeurs de termes/formules sur l'arithmétique cardinale RÉELLE (pas de théorème).
Léger : bonne formation + synonymies + theorie == 22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_definitions import (
    divise_cardinal, est_multiple_cardinal, est_diviseur_cardinal, reste_cardinal, quotient_cardinal)


def test_divise_est_existentiel():
    assert divise_cardinal("b", "a").tag == "exists"


def test_synonymies():
    # « a multiple de b » = « b diviseur de a » = « b divise a »
    assert est_multiple_cardinal("a", "b") == divise_cardinal("b", "a")
    assert est_diviseur_cardinal("b", "a") == divise_cardinal("b", "a")


def test_reste_quotient_sont_des_tau():
    assert reste_cardinal("a", "b").tag == "tau"
    assert quotient_cardinal("a", "b").tag == "tau"


def test_theorie_inchangee():
    divise_cardinal("b", "a"); reste_cardinal("a", "b"); quotient_cardinal("a", "b")
    assert len(E.theorie_ensembles().axiomes) == 22
