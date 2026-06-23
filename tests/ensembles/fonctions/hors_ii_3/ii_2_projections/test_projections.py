"""Tests V9 — §II.2 projections pr₁(x,y)=x, pr₂(x,y)=y et l'identité τx(x=a)=a."""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, tau
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import couple, pr1, pr2
from bourbaki.ensembles.fonctions.hors_ii_3.ii_2_projections.ensembles_projections import tau_egal, projection_premiere, projection_seconde


def test_tau_egal():
    a, x = var("a"), var("x")
    t = tau_egal("a", "x")
    assert t.conclusion == egal(tau("x", egal(x, a)), a) and t.est_clos


def test_projection_premiere():
    u, v = var("u"), var("v")
    t = projection_premiere("u", "v")
    assert t.conclusion == egal(pr1(couple(u, v)), u) and t.est_clos


def test_projection_seconde():
    u, v = var("u"), var("v")
    t = projection_seconde("u", "v")
    assert t.conclusion == egal(pr2(couple(u, v)), v) and t.est_clos
