# -*- coding: utf-8 -*-
"""Tests R5'c-U4 — l'équation de récursion passe à la réunion (2 hyps)."""
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_famille_rec import (
    Dfam_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_domaine_union import (
    antecedent_couverture_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_equation_union import (
    seg_inclus_seg, equation_union_rec,
)

_G, _E, _X, _Z = var("Gsr"), var("Esr"), var("xsr"), var("zeu")


def _vh(t):
    """Règle-itération jouet (opaque) : S = g(·)."""
    return E.valeur(var("gitr"), t)


def test_seg_inclus_seg():
    """{bo, z∈seg(x)} ⊢ seg(z) ⊂ seg(x)."""
    t = seg_inclus_seg()
    segx = E.segment_extremite(_G, _E, _X)
    segz = E.segment_extremite(_G, _E, _Z)
    assert t.conclusion == inclus(segz, segx)
    assert len(t.hypotheses) == 2
    assert len(E.theorie_ensembles().axiomes) == 22


def test_equation_union_rec():
    """🎯 U4 : {bo, antécédent} ⊢ equation_sur_seg(⋃Dfam_rec(x))."""
    t = equation_union_rec(_vh)
    U = union_famille(Dfam_rec(_G, _E, _X))
    assert t.conclusion == equation_sur_seg(U, _vh, _G, _E)
    hyps = list(t.hypotheses)
    assert len(hyps) == 2
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert antecedent_couverture_rec(_vh, "Gsr", "Esr", "xsr") in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
