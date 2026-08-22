# -*- coding: utf-8 -*-
"""Tests R2'a brique (iv) — égalité des restrictions au segment (7 hyps)."""
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_restrictions_egales import (
    hypothese_recurrence, restrictions_egales,
)

_P, _Q = var("pre"), var("qre")
_G, _E, _X, _Z = var("Gsr"), var("Esr"), var("xsr"), var("zsr")


def test_restrictions_egales():
    """{bo, func p, func q, doms, z∈dom_essai, HR} ⊢ p|seg z = q|seg z."""
    t = restrictions_egales()
    segz = E.segment_extremite(_G, _E, _Z)
    domx = dom_essai(_G, _E, _X)
    attendu = egal(E.restriction(_P, segz), E.restriction(_Q, segz))
    assert t.conclusion == attendu
    hyps = list(t.hypotheses)
    assert len(hyps) == 7
    assert E.est_bien_ordonne(_graphe_R(_G), _E) in hyps
    assert E.est_fonctionnel(_P) in hyps
    assert E.est_fonctionnel(_Q) in hyps
    assert egal(E.dom(_P), domx) in hyps
    assert egal(E.dom(_Q), domx) in hyps
    assert appartient(_Z, domx) in hyps
    assert hypothese_recurrence(_P, _Q, _G, _E, _Z) in hyps
    assert t.conclusion not in hyps
    assert len(E.theorie_ensembles().axiomes) == 22
