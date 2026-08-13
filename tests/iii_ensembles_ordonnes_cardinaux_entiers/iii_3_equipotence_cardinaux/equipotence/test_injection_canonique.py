# -*- coding: utf-8 -*-
"""Tests E.R.7 item 3 — injection canonique de A ⊂ E dans E."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, inclus
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_injection_de, inf_egal_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_injection_canonique import (
    injection_canonique, injection_canonique_theoreme, sous_ensemble_inf_egal)


def test_graphe_est_la_diagonale():
    assert injection_canonique("A") == E.diagonale(var("A"))


def test_injection_canonique_une_hypothese_honnete():
    th = injection_canonique_theoreme()
    assert th.conclusion == est_injection_de(E.diagonale(var("A")), var("A"), var("E"))
    assert th.hypotheses == frozenset({inclus(var("A"), var("E"))})


def test_corollaire_card_monotone():
    th = sous_ensemble_inf_egal()
    assert th.conclusion == inf_egal_card(var("A"), var("E"))
    assert th.hypotheses == frozenset({inclus(var("A"), var("E"))})
