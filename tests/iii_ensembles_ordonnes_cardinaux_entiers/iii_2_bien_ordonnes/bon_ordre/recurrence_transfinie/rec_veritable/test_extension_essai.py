# -*- coding: utf-8 -*-
"""Tests R3' brique 1 — la restriction efface le nouveau point (1 hyp)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, appartient,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_essai import (
    restriction_reunion_singleton_hors, x_hors_seg, restriction_pleine,
)

_P, _X, _V, _XX = var("pes"), var("xse"), var("vse"), var("Xse")


def test_restriction_reunion_singleton_hors():
    """{¬(x∈X)} ⊢ (p∪{(x,v)})|X = p|X — cible exacte, 1 hypothèse."""
    t = restriction_reunion_singleton_hors()
    pS = E.reunion(_P, E.singleton(E.couple(_X, _V)))
    attendu = egal(E.restriction(pS, _XX), E.restriction(_P, _XX))
    assert t.conclusion == attendu
    assert list(t.hypotheses) == [non(appartient(_X, _XX))]
    assert len(E.theorie_ensembles().axiomes) == 22


def test_x_hors_seg():
    """⊢ ¬(x ∈ seg(G,E,x)) — clos."""
    _G, _E, _Xs = var("Gsr"), var("Esr"), var("xsr")
    t = x_hors_seg()
    assert t.conclusion == non(appartient(_Xs, E.segment_extremite(_G, _E, _Xs)))
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_restriction_pleine():
    """{graphe p} ⊢ p|dom p = p — 1 hypothèse."""
    t = restriction_pleine()
    assert t.conclusion == egal(E.restriction(_P, E.dom(_P)), _P)
    assert list(t.hypotheses) == [E.est_un_graphe(_P)]
    assert len(E.theorie_ensembles().axiomes) == 22
