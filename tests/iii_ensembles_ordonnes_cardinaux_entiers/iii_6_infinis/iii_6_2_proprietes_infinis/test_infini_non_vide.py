# -*- coding: utf-8 -*-
"""Miroir de iii_6_2_proprietes_infinis/ensembles_infini_non_vide.py.

« Un ensemble infini a un élément » — l'hypothèse `a₀ ∈ A` que le Corollaire 1
porte, et que Bourbaki ne mentionne pas parce qu'elle découle de « A infini ».
Les trois théorèmes doivent être CLOS : c'est tout leur intérêt, un théorème
conditionnel ne déchargerait rien.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, existe, impl, appartient,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_infini_non_vide import (
    vide_est_fini, infini_implique_non_vide, infini_donne_element,
)


def test_vide_est_fini():
    """⊢ (A = ∅) ⇒ Fini(Card A), sans hypothèse.   [~1,5 s]"""
    vA = var("A")
    t = vide_est_fini("A")
    assert t.conclusion == impl(egal(vA, E.VIDE), est_fini(cardinal(vA)))
    assert not t.hypotheses, "doit être CLOS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_infini_implique_non_vide():
    """⊢ est_infini(Card A) ⇒ ¬(A = ∅), sans hypothèse.   [~1,5 s]

    `est_infini` étant DÉFINI comme ¬Fini (E III.6.1, Déf. 1), la contraposée
    de `vide_est_fini` tombe exactement sur la forme voulue. Le test le vérifie
    par égalité de formules : si la définition de `est_infini` changeait, il
    faudrait un pont, et ce test le signalerait."""
    vA = var("A")
    t = infini_implique_non_vide("A")
    assert t.conclusion == impl(est_infini(cardinal(vA)), non(egal(vA, E.VIDE)))
    assert not t.hypotheses, "doit être CLOS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_infini_donne_element():
    """🎯 ⊢ est_infini(Card A) ⇒ (∃z)(z ∈ A), sans hypothèse.   [~1,5 s]

    La forme que consomme le Corollaire 1 : de quoi éliminer `a₀ ∈ A` par
    ∃-élimination, la conclusion du corollaire ne mentionnant pas a₀."""
    vA = var("A")
    t = infini_donne_element("A")
    assert t.conclusion == impl(est_infini(cardinal(vA)),
                                existe("z", appartient(var("z"), vA)))
    assert not t.hypotheses, "doit être CLOS"
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
