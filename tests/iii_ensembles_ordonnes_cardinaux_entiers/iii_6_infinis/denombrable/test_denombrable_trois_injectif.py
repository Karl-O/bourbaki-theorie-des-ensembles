# -*- coding: utf-8 -*-
"""Tests §III.6 (prérequis Lemme 2) — W4 : n ↦ 3^n injective sur ℕ."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, impl
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_trois_injectif import (
    trois_puiss_injectif, _P3,
)


def test_trois_puiss_injectif():
    """🎯 W4 : ⊢ Fini n ⇒ ∀np((Fini np ∧ 3^n = 3^np) ⇒ n = np)."""
    vn = var("ntj")
    r = trois_puiss_injectif()
    assert not r.hypotheses
    assert r.conclusion == impl(est_fini(vn), _P3(vn))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
