# -*- coding: utf-8 -*-
"""Tests R8' étape 1 — l'itération sur ℕ par le critère C60-vrai."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ordre_NN_graphe import (
    G_ordre_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_unicite_globale import (
    est_solution_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_iteration_N import (
    regle_iteration_vraie, t_iter_en_vide, iteration_N_vrai,
)


def _S(t):
    """Le pas jouet (opaque) : S = s(·)."""
    return E.valeur(var("sitv"), t)


def test_t_iter_en_vide():
    """⊢ T_{S,a}(∅) = a — clos."""
    T = regle_iteration_vraie(_S, ZERO)
    t = t_iter_en_vide(_S, ZERO)
    assert t.conclusion == egal(T(E.VIDE), ZERO)
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_iteration_N_vrai():
    """🎯 {règle bornée} ⊢ (∃g)( sol(g, T_{S,a}, ≤, ℕ) ) — le bo DÉCHARGÉ."""
    t = iteration_N_vrai(_S, ZERO)
    T = regle_iteration_vraie(_S, ZERO)
    attendu = existe("gcap", est_solution_rec(var("gcap"), T, G_ordre_NN(), ensemble_NN()))
    assert t.conclusion == attendu
    assert list(t.hypotheses) == [regle_dans_V(T, "Vitv")]
    assert len(E.theorie_ensembles().axiomes) == 22
