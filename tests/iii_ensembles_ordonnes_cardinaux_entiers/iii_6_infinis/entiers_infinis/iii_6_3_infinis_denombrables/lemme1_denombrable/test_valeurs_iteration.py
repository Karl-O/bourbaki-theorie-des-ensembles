# -*- coding: utf-8 -*-
"""Tests K6c — valeurs dans E + déclampage (4 hyps)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, impl, appartient, pourtout, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_valeurs_iteration import (
    valeurs_dans_E, equation_declampee,
)

_U, _X0, _E, _G = var("uld"), var("xze"), var("Eld"), var("gcap")


def test_valeurs_dans_E():
    """{corps, x0∈E, u⊂E×E, dom u=E} ⊢ (∀n∈ℕ)(g(n)∈E)."""
    t = valeurs_dans_E(_U, _X0, _E)
    vn = var("nitv")
    attendu = pourtout("nitv", impl(appartient(vn, ensemble_NN()),
                                    appartient(E.valeur(_G, vn), _E)))
    assert t.conclusion == attendu
    assert len(t.hypotheses) == 4
    assert appartient(_X0, _E) in t.hypotheses
    assert inclus(_U, E.produit(_E, _E)) in t.hypotheses
    assert egal(E.dom(_U), _E) in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_equation_declampee():
    """🎯 K6c : {…} ⊢ (∀n∈ℕ)( g(succ n) = u(g(n)) ) — l'équation du livre."""
    t = equation_declampee(_U, _X0, _E)
    vn = var("nitv")
    attendu = pourtout("nitv", impl(
        appartient(vn, ensemble_NN()),
        egal(E.valeur(_G, successeur(vn)), E.valeur(_U, E.valeur(_G, vn)))))
    assert t.conclusion == attendu
    assert len(t.hypotheses) == 4
    assert len(E.theorie_ensembles().axiomes) == 22
