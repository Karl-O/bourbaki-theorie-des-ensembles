# -*- coding: utf-8 -*-
"""Tests récurrence forte (E III.33 var.1), DÉRIVÉE de C61 en trois maillons :
S{0} (vacuité) · S{n}⇒S{n+1} (Prop.2 + C58) · C61 sur S puis retour à R."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    app, var, appartient)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_variantes import (
    s_recurrence_forte, hypothese_recurrence_forte, conclusion_recurrence)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_forte_preuve import (
    s_forte_en_zero, heredite_s_forte, recurrence_forte)


def R(t):
    return app("Rrel", t)


def Rf(t):
    """R renvoyant une FORMULE (requis par les réécritures Leibniz s6 sur R{·})."""
    return appartient(t, var("Wrel"))


def test_s_zero_clos():
    th = s_forte_en_zero(R)
    assert th.conclusion == s_recurrence_forte(R, ZERO, "pfor")
    assert not th.hypotheses


def test_heredite_sous_H():
    th = heredite_s_forte(Rf)
    # une seule hypothèse : H = (∀n)(S{n} ⇒ R{n})
    assert th.hypotheses == frozenset({hypothese_recurrence_forte(Rf, "nfor", "pfor")})


def test_recurrence_forte_variante1():
    th = recurrence_forte(Rf)
    # conclusion == (∀n)(n entier ⇒ R{n}) ; 2 résidus honnêtes hérités de C61 :
    #   H = (∀n)(S{n}⇒R{n})  et  predecesseur_fini_universel (Prop.2 §III.5).
    assert th.conclusion == conclusion_recurrence(Rf, "nfor")
    assert len(th.hypotheses) == 2
    assert hypothese_recurrence_forte(Rf, "nfor", "pfor") in th.hypotheses
