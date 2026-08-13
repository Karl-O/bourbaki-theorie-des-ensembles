# -*- coding: utf-8 -*-
"""Test — T1c : { n∈ℕ, H2, H3, HW, HN } ⊢ factorielle_def2(succ n) = n!·(succ n).

Le pas de récurrence de la Déf. 2 (E III.41 L.30-32) sur le terme réel de T1a :
T1b-3 (u := famille large) + coïncidence des produits (a) + W_n = succ n (b) +
insertion Card (c).  HW/HN = pont fam↔valeur (opacité de valeur_famille, cf.
docstring du module).  theorie==22 avant/après.
slow : la route passe par appartenance_NN ⇒ N_existe (~5 min, mémoïsé/session).
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    appartient, egal, var,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import (
    _seg_NN, famille_successeurs, factorielle_def2,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_recursion import (
    hypotheses_graphes_recursion,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_factorielle_def2_rec import (
    hypothese_valuation_large, hypothese_valuation_etroite,
    valeur_large_au_point, produits_famille_coincident,
    factorielle_def2_recursion_enonce, factorielle_def2_recursion,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)

pytestmark = pytest.mark.slow


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_enonce_forme():
    """L'énoncé : (succ n)!_déf2 = produit_cardinal_binaire(n!_déf2, succ n), terme à terme."""
    vn = var("nfr")
    sn = successeur(vn)
    enonce = factorielle_def2_recursion_enonce()
    assert enonce == egal(factorielle_def2(sn), produit_cardinal_binaire(factorielle_def2(vn), sn))
    # LHS/RHS reconstruits INDÉPENDAMMENT au niveau Card/produit
    assert enonce.termes[0] == cardinal(E.produit_famille(famille_successeurs(sn), _seg_NN(sn)))
    assert enonce.termes[1] == cardinal(E.produit(
        cardinal(E.produit_famille(famille_successeurs(vn), _seg_NN(vn))), sn))


def test_valeur_large_au_point():
    """{ n∈ℕ, HW } ⊢ valeur_famille(W, n) = succ(n)   (route (b))."""
    thm = valeur_large_au_point("nfr")
    vn = var("nfr")
    W = famille_successeurs(successeur(vn))
    assert thm.conclusion == egal(E.valeur_famille(W, vn), successeur(vn))
    assert thm.hypotheses == frozenset({appartient(vn, ensemble_NN()),
                                        hypothese_valuation_large("nfr")})
    assert thm.conclusion not in thm.hypotheses


def test_produits_famille_coincident():
    """{ n∈ℕ, HW, HN } ⊢ ∏(W, seg n) = ∏(N, seg n)   (route (a))."""
    thm = produits_famille_coincident("nfr")
    vn = var("nfr")
    PW = E.produit_famille(famille_successeurs(successeur(vn)), _seg_NN(vn))
    PN = E.produit_famille(famille_successeurs(vn), _seg_NN(vn))
    assert thm.conclusion == egal(PW, PN)
    assert thm.hypotheses == frozenset({appartient(vn, ensemble_NN()),
                                        hypothese_valuation_large("nfr"),
                                        hypothese_valuation_etroite("nfr")})
    assert thm.conclusion not in thm.hypotheses


def test_factorielle_def2_recursion():
    """{ n∈ℕ, H2, H3, HW, HN } ⊢ factorielle_def2(succ n) = n!·(succ n)."""
    thm = factorielle_def2_recursion("nfr")
    vn = var("nfr")
    sn = successeur(vn)
    # conclusion == cible construite INDÉPENDAMMENT
    cible = egal(factorielle_def2(sn), produit_cardinal_binaire(factorielle_def2(vn), sn))
    assert thm.conclusion == cible
    assert thm.conclusion == factorielle_def2_recursion_enonce("nfr")
    # hypothèses HONNÊTES : exactement { n∈ℕ, H2, H3, HW, HN }
    W = famille_successeurs(sn)
    h2, h3 = hypotheses_graphes_recursion(W, vn)
    assert thm.hypotheses == frozenset({appartient(vn, ensemble_NN()), h2, h3,
                                        hypothese_valuation_large("nfr"),
                                        hypothese_valuation_etroite("nfr")})
    assert len(thm.hypotheses) == 5
    # non-VACUOUS + noyau intact
    assert thm.conclusion not in thm.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
