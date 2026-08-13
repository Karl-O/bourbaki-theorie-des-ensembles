"""Tests — 2^n et 3^n sont des entiers (prérequis Lemme 2 §III.6)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, impl
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, DEUX, TROIS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_puissance_deux_trois_NN import (
    deux_puissance_dans_NN, trois_puissance_dans_NN,
)


def test_deux_puissance_dans_NN():
    thm = deux_puissance_dans_NN("npdt")
    vn = var("npdt")
    cible = impl(est_fini(vn), est_fini(exposant_cardinal_binaire(DEUX, vn)))
    assert thm.est_clos
    assert thm.conclusion == cible
    assert thm.conclusion != est_fini(vn)  # non vacuous


def test_trois_puissance_dans_NN():
    thm = trois_puissance_dans_NN("npdt")
    vn = var("npdt")
    cible = impl(est_fini(vn), est_fini(exposant_cardinal_binaire(TROIS, vn)))
    assert thm.est_clos
    assert thm.conclusion == cible


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
