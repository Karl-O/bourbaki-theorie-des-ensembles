# -*- coding: utf-8 -*-
"""Test K6e — Eq(ℕ, g⟨ℕ⟩) : l'itérée est une bijection de ℕ sur son image."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_c63_vrai import (
    corps_c63_fort,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_regle_clampee import (
    regle_clampee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_equipotence_image import (
    equipotence_iteree,
)

_U, _X0, _E, _G = var("uld"), var("xze"), var("Eld"), var("gcap")


def test_equipotence_iteree():
    """🎯 K6e : {corps FORT + 5} ⊢ Eq(ℕ, g⟨ℕ⟩)."""
    t = equipotence_iteree(_U, _X0, _E)
    _, S_c = regle_clampee(_U, _X0, _E)
    NN = ensemble_NN()
    assert t.conclusion == equipotent(NN, E.image(_G, NN))
    assert len(t.hypotheses) == 6
    assert corps_c63_fort(S_c, _X0) in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
