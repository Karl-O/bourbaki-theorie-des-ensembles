# -*- coding: utf-8 -*-
"""Tests R5'a — coïncidence des essais récursifs (descente bilatérale)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_coincidence_famille import (
    point_dans_dom_essai, coincidence_essais_rec,
)

_P, _Q = var("pre"), var("qre")
_G, _E, _Y, _YP, _A = var("Gsr"), var("Esr"), var("ysr"), var("ypr"), var("acf")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_point_dans_dom_essai():
    """⊢ x ∈ dom_essai(G,E,x) — clos."""
    _X = var("xsr")
    t = point_dans_dom_essai()
    assert t.conclusion == appartient(_X, dom_essai(_G, _E, _X))
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_coincidence_essais_rec():
    """🎯 R5'a : {bo, essai p en y, essai q en y', a∈de(y), a∈de(y'), a∈E} ⊢ p(a)=q(a)."""
    t = coincidence_essais_rec(_vh)
    assert t.conclusion == egal(E.valeur(_P, _A), E.valeur(_Q, _A))
    hyps = list(t.hypotheses)
    assert len(hyps) == 6
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert est_essai_rec(_P, _vh, _G, _E, _Y) in hyps
    assert est_essai_rec(_Q, _vh, _G, _E, _YP) in hyps
    assert appartient(_A, dom_essai(_G, _E, _Y)) in hyps
    assert appartient(_A, dom_essai(_G, _E, _YP)) in hyps
    assert appartient(_A, _E) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
