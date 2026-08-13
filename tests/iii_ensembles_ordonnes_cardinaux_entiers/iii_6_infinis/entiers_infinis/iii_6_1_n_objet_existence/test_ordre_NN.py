# -*- coding: utf-8 -*-
"""Test n°63 — ℕ est ordonné par ≤ (est_relation_ordre_dans(R_N, ℕ)).

⚠️ LENT (~5 min) : la composante d'antisymétrie touche appartenance_NN ⇒ N_existe."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN import (
    ordre_NN, enonce_ordre_NN)


def test_ordre_NN():
    """⊢ est_relation_ordre_dans(R_N, ℕ) — CLOS, 0 hyp, theorie==22  (n°63)."""
    r = ordre_NN()
    assert r.conclusion == enonce_ordre_NN()
    assert r.est_clos
    assert r.hypotheses == frozenset()
    assert len(E.theorie_ensembles().axiomes) == 22
