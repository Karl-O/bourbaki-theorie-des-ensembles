# -*- coding: utf-8 -*-
"""Tests R8' étape 2 — l'évaluation en 0 : g(0)=a (1 hyp)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_unicite_globale import (
    est_solution_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_iteration_N import (
    regle_iteration_vraie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_iteration_eval import (
    valeur_zero_iteration,
)


def _S(t):
    """Le pas jouet (opaque) : S = s(·)."""
    return E.valeur(var("sitv"), t)


def test_valeur_zero_iteration():
    """🎯 {sol(g)} ⊢ g(0) = a — la première équation de C63."""
    t = valeur_zero_iteration(_S, ZERO)
    T = regle_iteration_vraie(_S, ZERO)
    assert t.conclusion == egal(E.valeur(var("gcap"), ZERO), ZERO)
    hyps = list(t.hypotheses)
    assert hyps == [est_solution_rec(var("gcap"), T, G_ordre_NN(), ensemble_NN())]
    assert len(E.theorie_ensembles().axiomes) == 22
