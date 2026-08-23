# -*- coding: utf-8 -*-
"""Test — ouvrir le maximal sans payer sa dérivation (règle perf)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import (
    a_implique_a,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_unpack_garde import (
    existence_maximal, unpack_sous_maximal,
)


def test_unpack_sous_maximal():
    """{(∃m) element_maximal} ⊢ C — les données du maximal servies à `derive`."""
    vu = []

    def derive(bij0, S_inc, S_inf, h_max, vS0, vphi0, p_eq):
        vu.append((bij0.conclusion, S_inc.conclusion, S_inf.conclusion))
        return a_implique_a(appartient(var("t"), var("T")))

    t = unpack_sous_maximal("E", derive)
    assert list(t.hypotheses) == [existence_maximal("E")]
    assert len(vu) == 1 and len(vu[0]) == 3      # les 3 données ont bien été servies
    assert "Smx" not in str(t.conclusion)        # témoins éliminés
    assert len(E.theorie_ensembles().axiomes) == 22
