# -*- coding: utf-8 -*-
"""Tests R3' assemblage — l'extension d'un pas de l'essai récursif (5 hyps)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_assemblage import (
    equation_sur_seg, extension_essai_rec,
)

_P, _G, _E, _X = var("pes"), var("Gsr"), var("Esr"), var("xsr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_extension_essai_rec():
    """🎯 R3' : {bo, func p, dom p=seg, graphe p, éq-seg} ⊢ est_essai_rec(p', x)."""
    t = extension_essai_rec(_vh)
    segx = E.segment_extremite(_G, _E, _X)
    pp = E.reunion(_P, E.singleton(E.couple(_X, _vh(_P))))
    assert t.conclusion == est_essai_rec(pp, _vh, _G, _E, _X)
    hyps = list(t.hypotheses)
    assert len(hyps) == 5
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert E.est_fonctionnel(_P) in hyps
    assert egal(E.dom(_P), segx) in hyps
    assert E.est_un_graphe(_P) in hyps
    assert equation_sur_seg(_P, _vh, _G, _E) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
