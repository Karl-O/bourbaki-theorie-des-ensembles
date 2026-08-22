# -*- coding: utf-8 -*-
"""Test K6d brique 3 — l'injectivité complète de l'itérée (6 hyps)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, impl, appartient, pourtout,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_injectivite_iteree import (
    x0_hors_image,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_injectivite_finale import (
    injectivite_iteree,
)

_U, _X0, _E, _G = var("uld"), var("xze"), var("Eld"), var("gcap")


def test_injectivite_iteree():
    """🎯 {6 hyps} ⊢ (∀n∈ℕ)(∀m∈ℕ)( g(m)=g(n) ⇒ m=n )."""
    t = injectivite_iteree(_U, _X0, _E)
    vm, vn = var("mitv"), var("nitv")
    NN = ensemble_NN()
    attendu = pourtout("nitv", impl(appartient(vn, NN),
        pourtout("mitv", impl(appartient(vm, NN),
            impl(egal(E.valeur(_G, vm), E.valeur(_G, vn)), egal(vm, vn))))))
    assert t.conclusion == attendu
    assert len(t.hypotheses) == 6
    assert x0_hors_image(_U, _X0, _E) in t.hypotheses
    assert E.injective_dans(_U, _E) in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
