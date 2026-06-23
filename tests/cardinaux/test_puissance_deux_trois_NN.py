"""Tests — 2^n et 3^n sont des entiers (prérequis Lemme 2 §III.6)."""
from bourbaki.logique.formule import var, impl
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, DEUX, TROIS
from bourbaki.cardinaux.ensembles_puissance_deux_trois_NN import (
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
