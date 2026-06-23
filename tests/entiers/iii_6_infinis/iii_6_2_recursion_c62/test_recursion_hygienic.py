"""Tests du wrapper α-hygiénique de récursion (O3).

Vérifie :
  • theorie_ensembles reste à 22 axiomes (noyau intact) ;
  • antecedent_dans_domaine_hygienic CLÔT la classe-quantificateur (F lie « y ») ;
  • il reproduit la conclusion du déposé sur un F « propre » ;
  • la classe-VALEUR (F lie le nom de la variable-valeur) est IRRÉDUCTIBLE par α
    (lève ValueError) — diagnostic O3 honnête, conforme à la docstring du module ;
  • la FACTORIELLE bute toujours sur O3 (le gluing déposé lève), confirmant que la
    capture factorielle est de classe-VALEUR, hors de portée du wrapper.
"""
import pytest

from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_1_termes_relations.formule import var, tau, egal
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege as E
from bourbaki.entiers.iii_6_infinis.iii_6_2_recursion_c62.ensembles_recursion_hygienic import (
    antecedent_dans_domaine_hygienic,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_hygienic_clot_F_propre():
    """F sans liant collisionnant : la version hygiénique clôt (concl ⇒, 0 hyp)."""
    r = antecedent_dans_domaine_hygienic("u", "v", "F")
    assert r.est_clos
    # conclusion = implication (u,v)∈F ⇒ u∈domF
    assert r.conclusion is not None


def test_hygienic_resout_y_class():
    """CLASSE-QUANTIFICATEUR : F lie internement « y » → le déposé capturerait ;
    le hygiénique CLÔT grâce au S5 frais-total + alpha_bridge."""
    F_y = tau("y", egal(var("w"), var("y")))          # τy(w=y) : F lie « y »
    r = antecedent_dans_domaine_hygienic("u", "v", F_y)
    assert r.est_clos                                  # 0 hypothèse résiduelle


def test_value_class_irreductible():
    """CLASSE-VALEUR : F lie le NOM de la variable-valeur « v » → le S5 substitue
    var('v') et est CAPTURÉ avant toute α-conversion → ValueError (O3 irréductible
    par α au niveau wrapper, conforme docstring point B)."""
    F_v = tau("v", egal(var("w"), var("v")))          # τv(w=v) : F lie « v »
    with pytest.raises(ValueError):
        antecedent_dans_domaine_hygienic("u", "v", F_v)


def test_factorielle_reste_bloquee_O3():
    """La factorielle bute TOUJOURS sur O3 (gluing déposé lève la τ-capture) :
    sa collision est de classe-VALEUR, hors de portée de l'α-hygiène wrapper."""
    from bourbaki.entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import (
        factorielle_essais_existe,
    )
    with pytest.raises(ValueError):
        factorielle_essais_existe()
