# -*- coding: utf-8 -*-
"""Tests R4'b — composition des restrictions (1 hyp)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_composition_restrictions import (
    composition_restrictions,
)

_P, _A, _B = var("pcr"), var("Acr"), var("Bcr")


def test_composition_restrictions():
    """{B⊂A} ⊢ (p|A)|B = p|B — cible exacte, 1 hypothèse."""
    t = composition_restrictions()
    attendu = egal(E.restriction(E.restriction(_P, _A), _B), E.restriction(_P, _B))
    assert t.conclusion == attendu
    assert list(t.hypotheses) == [inclus(_B, _A)]
    assert len(E.theorie_ensembles().axiomes) == 22
