# -*- coding: utf-8 -*-
"""Tests — associativité ITÉRÉE de l'addition cardinale (§III.3.3)."""
from __future__ import annotations

import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC, somme_disjointe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_iteree import (
    invariance_somme_gauche, invariance_somme_droite,
    somme_cardinale_associative_iteree,
)


def test_invariance_somme_gauche():
    """⊢ Card( Card(X) ⊔ Z ) = Card( X ⊔ Z ), clos et sans hypothèse."""
    x, z = var("Xinv"), var("Zinv")
    th = invariance_somme_gauche(x, z)
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == egal(cardinal(somme_disjointe(cardinal(x), z)),
                                 cardinal(somme_disjointe(x, z)))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_invariance_somme_droite():
    """⊢ Card( Z ⊔ Card(X) ) = Card( Z ⊔ X ), clos et sans hypothèse."""
    x, z = var("Xinvd"), var("Zinvd")
    th = invariance_somme_droite(x, z)
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == egal(cardinal(somme_disjointe(z, cardinal(x))),
                                 cardinal(somme_disjointe(z, x)))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_associativite_iteree():
    """⊢ (a+b)+c = a+(b+c) pour `somme_cardinale_binaire` — l'énoncé ITÉRÉ.

    C'est la forme dont l'addition a besoin pour être une OPÉRATION : le
    corollaire de la Prop. 5 ne parle que des sommes disjointes."""
    a, b, c = var("Aite"), var("Bite"), var("Cite")
    th = somme_cardinale_associative_iteree(a, b, c)
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == egal(SC(SC(a, b), c), SC(a, SC(b, c)))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_associativite_iteree_sur_des_termes():
    """Le lemme accepte des TERMES, pas seulement des noms de variables.

    C'est ce que les outils de recherche de preuve consomment : ils appliquent
    la loi à des sous-termes composés rencontrés en cours de route."""
    a, b, c, d = var("Ater"), var("Bter"), var("Cter"), var("Dter")
    gros = SC(a, b)
    th = somme_cardinale_associative_iteree(gros, c, d)
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == egal(SC(SC(gros, c), d), SC(gros, SC(c, d)))
    assert len(E.theorie_ensembles().axiomes) == 22
