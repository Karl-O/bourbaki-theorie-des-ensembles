# -*- coding: utf-8 -*-
"""Tests §III.6.3 — LEMME 2 : Eq(ℕ×ℕ, ℕ) (W6+W7, clôture)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)


def test_NN_carre_inf_egal_NN():
    """🎯 W6 : ⊢ ℕ×ℕ ≤ ℕ (l'injection de couplage)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_graphe_pairing import (
        NN_carre_inf_egal_NN)
    NN = ensemble_NN()
    r = NN_carre_inf_egal_NN()
    assert not r.hypotheses
    assert r.conclusion == inf_egal_card(E.produit(NN, NN), NN)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_lemme_deux_NN():
    """🎯🎯 LEMME 2 (E III.48) : ⊢ Eq(ℕ×ℕ, ℕ), clos."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_graphe_pairing import (
        lemme_deux_NN)
    NN = ensemble_NN()
    r = lemme_deux_NN()
    assert not r.hypotheses
    assert r.conclusion == equipotent(E.produit(NN, NN), NN)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
