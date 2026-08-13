# -*- coding: utf-8 -*-
"""Test Résumé E.R.14 item 8 — K⊂K' ⇔ (∀x) K(x)⊂K'(x)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_inclusion_coupes_er14 import (
    inclusion_ssi_coupes, enonce_inclusion_ssi_coupes)


def test_inclusion_ssi_coupes():
    """⊢ est_un_graphe(K) ⇒ (K⊂K' ⇔ (∀a) K{a}⊂K'{a}) — CLOS, 0 hyp."""
    r = inclusion_ssi_coupes()
    assert r.conclusion == enonce_inclusion_ssi_coupes()
    assert r.est_clos
    assert r.hypotheses == frozenset()


def test_theorie_inchangee():
    inclusion_ssi_coupes()
    assert len(E.theorie_ensembles().axiomes) == 22
