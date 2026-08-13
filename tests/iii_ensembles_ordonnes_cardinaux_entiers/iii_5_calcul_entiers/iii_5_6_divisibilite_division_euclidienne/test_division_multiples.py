# -*- coding: utf-8 -*-
"""Test §III.5.6 — stabilité des multiples (E III.39 L.27-31) : multiple d'un
multiple, somme de multiples.  Conclusions littérales, clôture, 22 axiomes."""
import pytest

from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_multiples as M

pytestmark = pytest.mark.slow


def test_multiple_de_multiple():
    """⊢ (a′ multiple de a et a multiple de b) ⇒ a′ multiple de b — clos, cible exacte."""
    t = M.multiple_de_multiple()
    assert t.conclusion == M.multiple_de_multiple_cible()
    assert t.est_clos
    assert t.hypotheses == frozenset()
    assert len(theorie_ensembles().axiomes) == 22


def test_somme_multiples():
    """⊢ (c multiple de b et d multiple de b) ⇒ (c+d) multiple de b — clos, cible exacte."""
    t = M.somme_multiples()
    assert t.conclusion == M.somme_multiples_cible()
    assert t.est_clos
    assert t.hypotheses == frozenset()
    assert len(theorie_ensembles().axiomes) == 22
