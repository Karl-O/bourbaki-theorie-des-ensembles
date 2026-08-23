# -*- coding: utf-8 -*-
"""Test de l'assemblage — le frame de Hessenberg a un élément maximal."""
import pytest
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_ordre, frame_pair,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_hess_garde import (
    donnees_recollement, hess_maximal,
)


@pytest.mark.slow
def test_hess_maximal():
    """🎯🎯 {E infini, données du recollement} ⊢ (∃m) element_maximal — LENT."""
    t = hess_maximal("E")
    vE = var("E")
    assert t.conclusion == existe("m", element_maximal(
        frame_ordre(vE), frame_pair(vE), var("m"), "x"))
    assert set(t.hypotheses) == {est_infini(cardinal(vE)),
                                 donnees_recollement("E")}
    assert len(E.theorie_ensembles().axiomes) == 22
