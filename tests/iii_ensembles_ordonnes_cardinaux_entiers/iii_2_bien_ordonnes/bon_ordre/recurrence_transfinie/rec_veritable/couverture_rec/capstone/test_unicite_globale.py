# -*- coding: utf-8 -*-
"""Tests R7' étape 4 — l'unicité globale de la solution (5 hyps)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_unicite_globale import (
    est_solution_rec, unicite_globale,
)

_G, _E, _GG, _H = var("Gsr"), var("Esr"), var("gcap"), var("hcap")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_unicite_globale():
    """🎯 {bo, sol(g), sol(h), graphe g, graphe h} ⊢ g = h."""
    t = unicite_globale(_vh)
    assert t.conclusion == egal(_GG, _H)
    hyps = list(t.hypotheses)
    assert len(hyps) == 5
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert est_solution_rec(_GG, _vh, _G, _E) in hyps
    assert est_solution_rec(_H, _vh, _G, _E) in hyps
    assert E.est_un_graphe(_GG) in hyps
    assert E.est_un_graphe(_H) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
