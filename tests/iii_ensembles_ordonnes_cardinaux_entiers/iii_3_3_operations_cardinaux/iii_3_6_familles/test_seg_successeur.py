# -*- coding: utf-8 -*-
"""Test — T1b-(1) : { n∈ℕ } ⊢ seg(ℕ, n+1) = seg(ℕ, n) ∪ {n}.   theorie==22.

slow : la route passe par appartenance_NN ⇒ N_existe (~5 min, mémoïsé/session).
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, egal, var,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import _seg_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_seg_successeur import (
    segment_succ_decomposition, segment_succ_decomposition_enonce,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN

pytestmark = pytest.mark.slow


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_segment_succ_decomposition():
    """{ n∈ℕ } ⊢ seg(n+1) = seg(n)∪{n} — cible exacte, 1 hyp honnête, non vacueux."""
    th = segment_succ_decomposition("nsg")
    vn = var("nsg")
    # conclusion == cible construite INDÉPENDAMMENT (segment de la chaîne C62)
    cible = egal(_seg_NN(successeur(vn)),
                 E.reunion(_seg_NN(vn), E.singleton(vn)))
    assert th.conclusion == cible
    assert th.conclusion == segment_succ_decomposition_enonce("nsg")
    # hypothèses HONNÊTES : exactement { n ∈ ℕ }
    assert th.hypotheses == frozenset({appartient(vn, ensemble_NN())})
    assert len(th.hypotheses) == 1
    # non-VACUOUS + noyau intact
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
