# -*- coding: utf-8 -*-
"""Test §III.6.1 — données d'ordre de ℕ ∀-closes (H1..H4).  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_donnees_ordre_NN import (
    h1_succ_dans_NN, h2_seg_succ_intervalle, h3_zero_dans_seg, h4_n_dans_seg,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_h1_succ_dans_NN():
    """⊢ (∀n)(Fini n ⇒ succ n∈ℕ) — CLOS (le miroir == est asserté dans le module)."""
    assert h1_succ_dans_NN().est_clos


def test_h2_seg_succ_intervalle():
    """⊢ (∀n)(Fini n ⇒ seg(ℕ,succ n)=[0,n]) — CLOS, le pont ∀-clos."""
    assert h2_seg_succ_intervalle().est_clos


def test_h3_zero_dans_seg():
    """⊢ (∀n)(Fini n ⇒ 0∈seg(ℕ,succ n)) — CLOS."""
    assert h3_zero_dans_seg().est_clos


def test_h4_n_dans_seg():
    """⊢ (∀n)(Fini n ⇒ n∈seg(ℕ,succ n)) — CLOS, theorie==22 après."""
    assert h4_n_dans_seg().est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_seg_zero_vide():
    """🎯 ⊢ seg(ℕ, ZERO) = ∅ — CLOS (« rien avant 0 »), cible à la main, theorie==22."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import egal
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import G_ordre_NN
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_donnees_ordre_NN import seg_zero_vide
    th = seg_zero_vide()
    assert th.conclusion == egal(
        E.segment_extremite(G_ordre_NN(), ensemble_NN(), ZERO), E.VIDE)
    assert th.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22
