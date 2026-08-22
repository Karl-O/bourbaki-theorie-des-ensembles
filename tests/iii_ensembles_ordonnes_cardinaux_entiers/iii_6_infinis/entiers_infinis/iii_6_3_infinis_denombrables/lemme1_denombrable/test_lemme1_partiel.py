# -*- coding: utf-8 -*-
"""Test K6g — le Lemme 1 sous hypothèses Dedekind : (∃D)(D⊂E ∧ Eq(D,ℕ))."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, existe, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_injectivite_iteree import (
    x0_hors_image,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_lemme1_partiel import (
    lemme1_sous_hypotheses,
)

_U, _X0, _E = var("uld"), var("xze"), var("Eld")


def test_lemme1_sous_hypotheses():
    """🎯 K6g : {6 hyps Dedekind} ⊢ (∃D)( D⊂E ∧ Eq(D,ℕ) )."""
    t = lemme1_sous_hypotheses(_U, _X0, _E)
    vD = var("Dld")
    NN = ensemble_NN()
    attendu = existe("Dld", et(inclus(vD, _E), equipotent(vD, NN)))
    assert t.conclusion == attendu
    assert len(t.hypotheses) == 6
    assert x0_hors_image(_U, _X0, _E) in t.hypotheses
    assert E.injective_dans(_U, _E) in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
