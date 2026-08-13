# -*- coding: utf-8 -*-
"""Test — T1b-(3) : { n∈ℕ, H2, H3 } ⊢ Card(∏_{seg(n+1)} u) = Card((∏_{seg n} u) × u_n).

L'assemblage T1b-1 + congruence-trou + T1b-2 (I:=seg(ℕ,n), j:=n), H1 déchargée
par point_hors_segment.  theorie==22 avant/après.
slow : la route passe par appartenance_NN ⇒ N_existe (~5 min, mémoïsé/session).
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, egal, var,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, produit_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import _seg_NN
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction import (
    hypothese_indice_neuf, hypothese_graphes_total, hypothese_graphes_partiel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_recursion import (
    produit_fini_recursion, produit_fini_recursion_enonce, hypotheses_graphes_recursion,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN

pytestmark = pytest.mark.slow


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_enonce_forme_cardinale():
    """L'énoncé : LHS = ∏ Déf.3 sur seg(n+1) ; RHS = produit_cardinal_binaire terme-à-terme."""
    vu, vn = var("upr"), var("npr")
    enonce = produit_fini_recursion_enonce()
    assert enonce == egal(cardinal(E.produit_famille(vu, _seg_NN(successeur(vn)))),
                          produit_cardinal_binaire(E.produit_famille(vu, _seg_NN(vn)),
                                                   E.valeur_famille(vu, vn)))
    # LHS EST le produit de famille de la Déf. 3 §III.3.3 (celui de factorielle_def2)
    assert enonce.termes[0] == produit_cardinal(vu, _seg_NN(successeur(vn)))
    # RHS EST Card du produit binaire (forme cardinale exacte, comme T1b-2)
    assert enonce.termes[1] == cardinal(E.produit(E.produit_famille(vu, _seg_NN(vn)),
                                                  E.valeur_famille(vu, vn)))


def test_produit_fini_recursion():
    """{ n∈ℕ, H2, H3 } ⊢ Card(∏_{seg(n+1)}) = Card(∏_{seg n} × u_n) — H1 déchargée."""
    thm = produit_fini_recursion("upr", "npr")
    vu, vn = var("upr"), var("npr")
    I = _seg_NN(vn)
    # conclusion == cible construite INDÉPENDAMMENT
    cible = egal(cardinal(E.produit_famille(vu, _seg_NN(successeur(vn)))),
                 produit_cardinal_binaire(E.produit_famille(vu, I),
                                          E.valeur_famille(vu, vn)))
    assert thm.conclusion == cible
    assert thm.conclusion == produit_fini_recursion_enonce("upr", "npr")
    # hypothèses HONNÊTES : exactement { n∈ℕ, H2, H3 }
    h2, h3 = hypotheses_graphes_recursion("upr", "npr")
    assert h2 == hypothese_graphes_total(vu, I, vn)
    assert h3 == hypothese_graphes_partiel(vu, I, vn)
    assert thm.hypotheses == frozenset({appartient(vn, ensemble_NN()), h2, h3})
    assert len(thm.hypotheses) == 3
    # H1 = n∉seg(ℕ,n) est bien DÉCHARGÉE (point_hors_segment)
    assert hypothese_indice_neuf(I, vn) not in thm.hypotheses
    # non-VACUOUS + noyau intact
    assert thm.conclusion not in thm.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
