# -*- coding: utf-8 -*-
"""Tests R4'a — la restriction d'un essai récursif descend (3 hyps)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, inclus, appartient,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_restriction_essai import (
    dom_essai_monotone, restriction_essai_rec,
)

_P, _G, _E, _X, _Y = var("pes"), var("Gsr"), var("Esr"), var("xsr"), var("ysr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_dom_essai_monotone():
    """{bo, y∈dom_essai(x)} ⊢ dom_essai(y) ⊂ dom_essai(x)."""
    t = dom_essai_monotone()
    assert t.conclusion == inclus(dom_essai(_G, _E, _Y), dom_essai(_G, _E, _X))
    hyps = list(t.hypotheses)
    assert len(hyps) == 2
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert appartient(_Y, dom_essai(_G, _E, _X)) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22


def test_restriction_essai_rec():
    """🎯 R4'a : {bo, essai p en x, y∈dom_essai(x)} ⊢ est_essai_rec(p|dom_essai(y), y)."""
    t = restriction_essai_rec(_vh)
    pD = E.restriction(_P, dom_essai(_G, _E, _Y))
    assert t.conclusion == est_essai_rec(pD, _vh, _G, _E, _Y)
    hyps = list(t.hypotheses)
    assert len(hyps) == 3
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert est_essai_rec(_P, _vh, _G, _E, _X) in hyps
    assert appartient(_Y, dom_essai(_G, _E, _X)) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
