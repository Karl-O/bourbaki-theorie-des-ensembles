# -*- coding: utf-8 -*-
"""Tests H1 — l'amorçage du frame de Zorn : 𝔉(E) ≠ ∅."""
import pytest
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini, est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_maximal_clos import (
    residu_H1,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.decharge.ensembles_h1 import (
    eq_DD_D, temoin_frame, h1_decharge,
)

_D, _E = var("Dld"), var("Eld")


def test_temoin_frame():
    """{D⊂E, Eq(D,ℕ), Lemme 2} ⊢ (∃x)(x∈𝔉(E)) — étapes 1-4, Lemme 2 en hyp."""
    t0 = eq_DD_D("Dld")
    assert t0.conclusion == equipotent(E.produit(_D, _D), _D)
    t = temoin_frame("Dld", "Eld")
    NN = ensemble_NN()
    assert t.conclusion == residu_H1("Eld")
    assert set(t.hypotheses) == {inclus(_D, _E), equipotent(_D, NN),
                                 equipotent(E.produit(NN, NN), NN),
                                 est_infini_ensemble(NN)}
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_h1_decharge():
    """🎯 H1 : {est_infini(Card E)} ⊢ (∃x)(x∈𝔉(E)) — Lemmes 1 et 2 (TRÈS LENT)."""
    t = h1_decharge("Eld")
    assert t.conclusion == residu_H1("Eld")
    assert list(t.hypotheses) == [est_infini(cardinal(_E))]
    assert len(E.theorie_ensembles().axiomes) == 22
