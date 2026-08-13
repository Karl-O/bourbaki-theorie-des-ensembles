# -*- coding: utf-8 -*-
"""Test §III.5.6 Th.1 — division euclidienne, existence (bricks _pas_petit / _pas_grand).

R{cible} := (∃q)(∃r)(b·q+r=cible et r<b).  Deux pas de la récurrence forte sur a."""
import pytest
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import appartient, var
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence import (
    _pas_petit, enonce_pas_petit, _assoc_binaire, _pas_grand, enonce_pas_grand)

pytestmark = pytest.mark.slow


def test_pas_petit():
    """⊢ {a fini} (a<b) ⇒ R{a}  (cas a<b, q=0 r=a)."""
    r = _pas_petit()
    assert r.conclusion == enonce_pas_petit()
    assert r.hypotheses == frozenset([est_fini(var("a"))])


def test_assoc_binaire():
    """⊢ (x+y)+z = x+(y+z)  (associativité somme cardinale binaire), CLOS."""
    r = _assoc_binaire()
    assert r.est_clos


def test_pas_grand():
    """⊢ {a fini, b fini, b≤a, R{a−b}} R{a}  (cas a≥b, recomposition)."""
    r = _pas_grand()
    assert r.conclusion == enonce_pas_grand()[1]
    assert len(r.hypotheses) == 4


def test_theorie_inchangee():
    _pas_petit()
    assert len(E.theorie_ensembles().axiomes) == 22
