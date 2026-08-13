# -*- coding: utf-8 -*-
"""Test E.R.20 item 8 (n°92) — (⋂X_ι)×(⋂Y_ι)=⋂(X_ι×Y_ι) mêmes indices."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_2_proprietes.ensembles_produit_inter_familles_er20 import (
    produit_inter_familles, enonce_produit_inter_familles,
    hyp_produit_famille, _dir_produit_vers_interH)


def test_produit_inter_familles():
    """⊢ (¬(I=∅) et ∀i H_i=X_i×Y_i) ⇒ (⋂X)×(⋂Y)=⋂H — CLOS, 0 hyp."""
    r = produit_inter_familles()
    assert r.conclusion == enonce_produit_inter_familles()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_sens_direct_sans_hypothese_de_non_vacuite():
    """VERROU : le sens ⇒ tient UNE hypothèse — pas de ¬(I=∅) « par réflexe ».

    Le témoin d'indice qu'exige l'introduction dans ⋂H depuis la Déf. 2
    (⋂ = sélection dans ⋃) est GRATUIT ici : le corps de l'existentiel porte déjà
    p∈⋂_{ι∈I} X_ι, et ⋂ ⊂ ⋃ en donne (∃i)(i∈I et p∈X_i).  Ré-ajouter ¬(I=∅)
    serait un affaiblissement gratuit de l'énoncé du lemme."""
    d = _dir_produit_vers_interH()
    assert d.hypotheses == frozenset({hyp_produit_famille()})


def test_theorie_inchangee():
    produit_inter_familles()
    assert len(E.theorie_ensembles().axiomes) == 22
