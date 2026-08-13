# -*- coding: utf-8 -*-
"""Test §III.5.6 — recomposition du pas de récurrence de la division euclidienne.

On APPELLE le théorème : conditionnel HONNÊTE (4 hypothèses reconstruites : garde cardinale,
ordre b≤a, HR a−b = b·q+r), conclusion == cible b + (b·q+r) = a, theorie == 22.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import (
    diff_somme)
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_pas as M

pytestmark = pytest.mark.slow


def test_division_pas_recomposition():
    """{est_cd b, est_cd a, b≤a, a−b=b·q+r} ⊢ b + (b·q+r) = a — hyps honnêtes, 22 axiomes."""
    t = M.division_pas_recomposition()
    va, vb, vq, vr = var("a"), var("b"), var("q"), var("r")
    assert t.conclusion == M.division_pas_recomposition_cible()
    assert not t.est_clos                               # conditionnel honnête
    bqr = somme_cardinale_binaire(produit_cardinal_binaire(vb, vq), vr)
    attendues = {
        et(et(est_cardinal(vb), est_cardinal(va)), inf_egal_card(vb, va)),
        egal(diff_somme(va, vb, "c"), bqr),
    }
    assert set(t.hypotheses) == attendues
    assert len(theorie_ensembles().axiomes) == 22
