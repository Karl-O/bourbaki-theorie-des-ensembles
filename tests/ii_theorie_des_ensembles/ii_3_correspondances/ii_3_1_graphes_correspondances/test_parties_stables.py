# -*- coding: utf-8 -*-
"""Tests E.R.7 item 4 — parties stables par f / par un ensemble 𝔉."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, impl, pourtout, appartient, inclus)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_1_graphes_correspondances.ensembles_parties_stables import (
    est_stable_par, est_stable_par_ensemble)


def test_stable_par_f():
    X, f = var("X"), var("f")
    assert est_stable_par(X, f) == inclus(E.image(f, X), X)


def test_stable_par_ensemble():
    X, F = var("X"), var("F")
    vf = var("fstb")
    attendu = pourtout("fstb", impl(appartient(vf, F),
                                    inclus(E.image(vf, X), X)))
    assert est_stable_par_ensemble(X, F) == attendu
