# -*- coding: utf-8 -*-
"""§III.5.6 — LA DIVISION EUCLIDIENNE N'EST PLUS VIDE (R-12).

Ces tests portent sur le mode `cardinal=True`, qui mesure la récurrence forte
avec `diff_cardinale` (le τ GARDÉ) au lieu de `diff_somme`.

CE QU'ILS ÉTABLISSENT, et qu'aucun test existant ne pouvait voir : l'absence de
la ∀∀-clôture NUE de `cardinal_pas_entre`. Les théorèmes historiques concluent
exactement les mêmes formules — mais en s'appuyant sur cette hypothèse NON
SATISFAITE, ce qui les rend vrais et VIDES (ANOMALIES 2026-08-23). Seule
l'inspection des hypothèses distingue les deux.

⚠️ TRÈS LENTS (mesuré : 926 s et 1491 s). L'existence rejoue toute la récurrence
forte, qui invoque `_diff_strict` deux fois.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, pourtout, libres_f,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    cardinal_pas_entre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence_final import (
    division_existence, enonce_division_existence,
    division_euclidienne, enonce_division_euclidienne,
)

_NUE = pourtout("c", pourtout("b", cardinal_pas_entre(var("b"), var("c"))))


@pytest.mark.slow
def test_existence_sans_hypothese_fausse():
    """🎯 { est_cardinal(b), b ≠ 0 } ⊢ (∀n)(Fini n ⇒ (∃q)(∃r)(b·q+r=n et r<b)).

    Deux hypothèses, et l'universel nu absent.   [~930 s]"""
    t = division_existence("bdf", cardinal=True)
    assert t.conclusion == enonce_division_existence("bdf")
    assert _NUE not in t.hypotheses, \
        "l'hypothèse NON SATISFAITE est revenue — le théorème serait vide"
    assert len(t.hypotheses) == 2, "hyps : %d" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_theoreme_complet_sans_hypothese_fausse():
    """🎯🎯 THÉORÈME 1 §III.5.6 COMPLET, sous les SEULES hypothèses du livre.

    { Fini a, Fini b, 0 < b } — exactement E III.39 L.10. Aucun résidu C61,
    aucun témoin résiduel (chaque hypothèse ne mentionne qu'une variable).
    [~1490 s]"""
    va, vb = var("adf"), var("bdf")
    t = division_euclidienne("adf", "bdf", cardinal=True)
    assert t.conclusion == enonce_division_euclidienne("adf", "bdf")
    assert _NUE not in t.hypotheses, \
        "l'hypothèse NON SATISFAITE est revenue — le théorème serait vide"
    assert set(t.hypotheses) == {est_fini(va), est_fini(vb),
                                 inf_strict_card(ZERO, vb)}, \
        "hypothèses résiduelles inattendues : %d" % len(t.hypotheses)
    #  aucun témoin résiduel : chaque hypothèse ne parle que d'UNE variable
    assert all(len(libres_f(h)) == 1 for h in t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
