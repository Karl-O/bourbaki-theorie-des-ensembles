# -*- coding: utf-8 -*-
"""Tests — θ_{R_f} caractérise R_f (réciproque du passage au quotient)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ii_6_5_decomposition.ensembles_theta_caracterise import (
    theta_temoin, theta_injectif,
)


def test_theta_temoin():
    """{x∈E} ⊢ R_f{x, θ(x)} — x est dans sa propre classe (témoin canonique)."""
    assert len(theta_temoin().hypotheses) == 1


def test_theta_injectif():
    """🎯 RÉCIPROQUE : {x∈E, y∈E, θ(x)=θ(y)} ⊢ f(x)=f(y) — 3 hyps."""
    th = theta_injectif()
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
