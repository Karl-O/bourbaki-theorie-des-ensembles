# -*- coding: utf-8 -*-
"""Test §III.5.6 — (a = b·q) ⇒ (q = a/b) : le τ-quotient caractérisé.

Première consommation du Théorème 1 complet (l'unicité identifie q au τ).
Résidus déclarés : Fini(a/b) + C61 (mêmes classes que le Th.1)."""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E

pytestmark = pytest.mark.slow


def test_quotient_de_produit():
    """⊢ {Fini b, Fini q, Fini(a/b), 0<b, +C61} (a=b·q) ⇒ (q=a/b), énoncé asserté."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_quotient import (
        quotient_de_produit, enonce_quotient_de_produit)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_definitions import (
        quotient_cardinal)
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini

    r = quotient_de_produit()
    assert r.conclusion == enonce_quotient_de_produit()
    #   les résidus déclarés sont là — et l'hypothèse a=b·q est bien DÉCHARGÉE
    assert est_fini(quotient_cardinal(var("aqt"), var("bqt"))) in r.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
