"""Tests §III.5.8 — FACTORIELLE (E III.41, Déf. 2) : caractérisation récursive."""
from bourbaki.logique.i_1_termes_relations.formule import app, var, egal, impl, pourtout
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO, UN
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_iii5 import (
    factorielle_zero_relation, factorielle_succ_relation, factorielle_entier_de,
)


def _f(x):
    """Terme-fonction OPAQUE de test : f(x) := app('myfac', x)."""
    return app("myfac", x)


def test_theorie_22():
    factorielle_entier_de(_f)
    assert len(theorie_ensembles().axiomes) == 22


def test_factorielle_entier_de_conclusion():
    thm = factorielle_entier_de(_f)
    cible = pourtout("nfe", impl(est_fini(var("nfe")),
                                 est_fini(_f(var("nfe")))))
    assert thm.conclusion == cible


def test_factorielle_entier_de_hyps_honnetes():
    """Les DEUX prémisses caractérisantes (R0),(Rs) sont les hypothèses ; non vacuous."""
    thm = factorielle_entier_de(_f)
    R0 = factorielle_zero_relation(_f)                 # f(0)=1
    Rs = factorielle_succ_relation(_f, n="nfac")       # (∀n)(Fini n ⇒ f(n+1)=(n+1)·f(n))
    assert R0 in thm.hypotheses
    assert Rs in thm.hypotheses
    assert thm.conclusion not in thm.hypotheses        # JAMAIS vacuous


def test_relations_formes():
    """R0 = f(0)=1 ; Rs = récurrence (n+1)!=n!·(n+1) avec 1=UN=succ(0)."""
    assert factorielle_zero_relation(_f) == egal(_f(ZERO), UN)
    vn = var("nfac")
    assert factorielle_succ_relation(_f) == pourtout(
        "nfac", impl(est_fini(vn),
                     egal(_f(successeur(vn)),
                          produit_cardinal_binaire(successeur(vn), _f(vn)))))
