# -*- coding: utf-8 -*-
"""Tests R2'a brique (ii) — seg-transitivité et inclusion dans dom_essai."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, impl, appartient, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_recurrence_transfinie import (
    _graphe_R,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import (
    dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_seg_transitif import (
    seg_transitif_strict, seg_inclus_dom_essai,
)

_G, _E, _X, _Z, _U = var("Gsr"), var("Esr"), var("xsr"), var("zsr"), var("usr")
_BO = E.est_bien_ordonne(_graphe_R(_G), _E)


def test_seg_transitif_strict():
    """{bo} ⊢ (z∈seg(x) ∧ u∈seg(z)) ⇒ u∈seg(x) — cible exacte, 1 hypothèse."""
    t = seg_transitif_strict()
    segx = E.segment_extremite(_G, _E, _X)
    segz = E.segment_extremite(_G, _E, _Z)
    attendu = impl(et(appartient(_Z, segx), appartient(_U, segz)),
                   appartient(_U, segx))
    assert t.conclusion == attendu
    assert list(t.hypotheses) == [_BO]
    assert len(E.theorie_ensembles().axiomes) == 22


def test_seg_inclus_dom_essai():
    """{bo} ⊢ z∈dom_essai(x) ⇒ seg(z) ⊂ dom_essai(x) — cible exacte, 1 hypothèse."""
    t = seg_inclus_dom_essai()
    segz = E.segment_extremite(_G, _E, _Z)
    domx = dom_essai(_G, _E, _X)
    attendu = impl(appartient(_Z, domx), inclus(segz, domx))
    assert t.conclusion == attendu
    assert list(t.hypotheses) == [_BO]
    assert len(E.theorie_ensembles().axiomes) == 22
