# -*- coding: utf-8 -*-
"""Tests R5'c-U1 — la famille des essais récursifs est compatible (1 hyp bo)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    famille_compatible,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_famille_rec import (
    Dfam_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_union_rec import (
    compatibilite_Dfam_rec,
)

_G, _E, _X = var("Gsr"), var("Esr"), var("xsr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_compatibilite_Dfam_rec():
    """🎯 R5'c-U1 : {bo} ⊢ famille_compatible(Dfam_rec(x)) — 1 hypothèse."""
    t = compatibilite_Dfam_rec(_vh)
    assert t.conclusion == famille_compatible(Dfam_rec(_G, _E, _X))
    hyps = list(t.hypotheses)
    assert hyps == [E.est_bien_ordonne(_graphe_R(_G), _E)]
    assert len(E.theorie_ensembles().axiomes) == 22
