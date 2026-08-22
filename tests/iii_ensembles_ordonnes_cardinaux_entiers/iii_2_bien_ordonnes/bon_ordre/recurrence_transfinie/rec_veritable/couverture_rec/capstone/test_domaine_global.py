# -*- coding: utf-8 -*-
"""Tests R7' étape 2 — dom f = E (la solution globale est partout définie)."""
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_capstone_rec import (
    Dglob_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_domaine_global import (
    dom_f_inclus_E, dom_f_egal_E,
)

_G, _E = var("Gsr"), var("Esr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_dom_f_inclus_E():
    """⊢ dom f ⊂ E — clos."""
    t = dom_f_inclus_E(_vh)
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_dom_f_egal_E():
    """🎯 {bo, règle bornée} ⊢ dom(⋃Dglob) = E."""
    t = dom_f_egal_E(_vh)
    f = union_famille(Dglob_rec(_G, _E))
    assert t.conclusion == egal(E.dom(f), _E)
    hyps = list(t.hypotheses)
    assert len(hyps) == 2
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert regle_dans_V(_vh) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
