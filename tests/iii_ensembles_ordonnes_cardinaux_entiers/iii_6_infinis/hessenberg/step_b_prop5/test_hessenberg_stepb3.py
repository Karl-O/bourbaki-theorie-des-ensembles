# -*- coding: utf-8 -*-
"""Tests — STEP B2-RÉUNION : ¬(𝔟<Card E) sous maximal-data, Ucadre ÉLIMINÉ.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, non, libres_f,
)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.step_b_prop5.ensembles_hessenberg_stepb3 import (
    negation_strict_sous_maximal_reunion,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_b2_reunion_ucadre_elimine():
    """🎯🎯 ¬(Card S₀ < Card E) — l'élimination de Ucadre ABOUTIT : 7 hyps, toutes
    Ucadre/psi/uwit-LIBRES (maximal-data + hyps propres + résidus ∀∀)."""
    th = negation_strict_sous_maximal_reunion()
    assert th.conclusion == non(inf_strict_card(cardinal(var("S0")), cardinal(var("E"))))
    assert len(th.hypotheses) == 7
    for h in th.hypotheses:
        interdits = {"Ucadre", "psi", "uwit"} & set(libres_f(h))
        assert not interdits, f"témoin fuité {interdits}"
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
