"""Test §II.4.5 — commutativité de la réunion / intersection binaires."""
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_1_definitions_algebre.ensembles_binaire_commut_ii4 import (
    commutativite_reunion_binaire, cible_commutativite_reunion_binaire,
    commutativite_inter_binaire, cible_commutativite_inter_binaire)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def test_commutativite_reunion_binaire_close():
    thm = commutativite_reunion_binaire()
    assert thm.est_clos
    assert thm.hypotheses == frozenset()
    assert thm.conclusion == cible_commutativite_reunion_binaire()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_commutativite_inter_binaire_close():
    thm = commutativite_inter_binaire()
    assert thm.est_clos
    assert thm.hypotheses == frozenset()
    assert thm.conclusion == cible_commutativite_inter_binaire()
    assert len(E.theorie_ensembles().axiomes) == 22
