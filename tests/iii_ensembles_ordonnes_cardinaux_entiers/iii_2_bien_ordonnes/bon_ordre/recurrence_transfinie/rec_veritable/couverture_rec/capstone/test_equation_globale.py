# -*- coding: utf-8 -*-
"""Tests R7' étape 3 — l'équation de récursion vaut partout sur f."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_assemblage import (
    equation_sur_seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_capstone_rec import (
    Dglob_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_equation_globale import (
    seg_inclus_E, equation_f,
)

_G, _E, _X = var("Gsr"), var("Esr"), var("xsr")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_seg_inclus_E():
    """⊢ seg(x) ⊂ E — clos."""
    t = seg_inclus_E()
    assert t.conclusion == inclus(E.segment_extremite(_G, _E, _X), _E)
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_equation_f():
    """🎯 {bo, règle bornée} ⊢ (∀z∈dom f)( f(z) = vh(f|seg z) )."""
    t = equation_f(_vh)
    f = union_famille(Dglob_rec(_G, _E))
    assert t.conclusion == equation_sur_seg(f, _vh, _G, _E)
    hyps = list(t.hypotheses)
    assert len(hyps) == 2
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert regle_dans_V(_vh) in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
