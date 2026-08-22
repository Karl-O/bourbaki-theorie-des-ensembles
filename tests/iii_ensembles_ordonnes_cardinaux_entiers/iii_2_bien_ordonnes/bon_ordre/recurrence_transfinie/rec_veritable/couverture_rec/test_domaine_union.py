# -*- coding: utf-8 -*-
"""Tests R5'c U2/U3 — le domaine de la réunion ⋃Dfam_rec(x)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_famille_rec import (
    Dfam_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_domaine_union import (
    antecedent_couverture_rec, dom_union_rec,
)

_G, _E, _X = var("Gsr"), var("Esr"), var("xsr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_dom_union_rec():
    """🎯 U-dom : {bo, antécédent} ⊢ dom(⋃Dfam_rec(x)) = seg(x)."""
    t = dom_union_rec(_vh)
    U = union_famille(Dfam_rec(_G, _E, _X))
    assert t.conclusion == egal(E.dom(U), E.segment_extremite(_G, _E, _X))
    hyps = list(t.hypotheses)
    assert len(hyps) == 2
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert antecedent_couverture_rec(_vh, "Gsr", "Esr", "xsr") in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
