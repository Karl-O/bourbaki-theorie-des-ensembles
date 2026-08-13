# -*- coding: utf-8 -*-
"""Tests — factorisation universelle par le quotient (C57 + R_f).  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_decomposition_c57 import (
    compatible_avec_R_associee, factorisation_universelle,
)


def test_compatible_avec_R_associee():
    """f est compatible avec la relation qu'elle induit — CLOS."""
    assert compatible_avec_R_associee().est_clos


def test_factorisation_universelle():
    """👑 Toute application se factorise par son quotient : H(p(x))=f(x) — 2 hyps."""
    th = factorisation_universelle()
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
