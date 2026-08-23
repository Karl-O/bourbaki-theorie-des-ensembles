# -*- coding: utf-8 -*-
"""Miroir de iii_6_2_proprietes_infinis/ensembles_absorption_generale.py.

L'absorption a + a = a pour un cardinal infini QUELCONQUE — là où le dépôt ne
l'avait qu'au maximal de Zorn.

Le dernier test est un test de NON-RÉGRESSION : `absorption_au_maximal` a été
refactorée (son cœur extrait en `absorption_depuis_carre`) et doit continuer de
conclure exactement comme avant. Sans lui, l'extraction serait un pari.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_absorption_generale import (
    enonce_absorption_generale, carre_depuis_hessenberg,
    absorption_sous_hessenberg,
)


def test_carre_depuis_hessenberg():
    """Le carré 𝔞·𝔞 = 𝔞 est EXACTEMENT le conséquent du Th. 2.   [instantané]

    Si ce test tombe, c'est que l'énoncé de Hessenberg a changé de forme, et le
    modus ponens devient un pont à construire."""
    vA = var("A")
    cA = cardinal(vA)
    t = carre_depuis_hessenberg("A")
    assert t.conclusion == egal(produit_cardinal_binaire(cA, cA), cA)
    assert set(t.hypotheses) == {enonce_hessenberg("A"), est_infini(cA)}
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_absorption_sous_hessenberg():
    """🎯 { Th. 2, A infini } ⊢ Card A + Card A = Card A.   [~185 s]

    L'absorption pour un cardinal infini quelconque. Deux hypothèses, et deux
    seulement : le Théorème 2 (porté, non dérivé — RÈGLE PERF, 5172,8 s) et
    l'infinité de A."""
    vA = var("A")
    t = absorption_sous_hessenberg("A")
    assert t.conclusion == enonce_absorption_generale("A")
    assert set(t.hypotheses) == {enonce_hessenberg("A"), est_infini(cardinal(vA))}, \
        "hypothèses résiduelles inattendues : %d" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


@pytest.mark.slow
def test_non_regression_absorption_au_maximal():
    """NON-RÉGRESSION : la version au maximal survit à l'extraction.   [~55 s]

    `absorption_au_maximal` a vu son cœur extrait en `absorption_depuis_carre`
    pour être partagé avec la version globale. Aucune ligne de raisonnement n'a
    changé — ce test l'établit plutôt que de le supposer."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_absorption import (
        absorption_au_maximal, enonce_absorption,
    )
    t = absorption_au_maximal()
    assert t.conclusion == enonce_absorption("S0")
    assert len(t.hypotheses) == 2, "hyps : %d" % len(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22
