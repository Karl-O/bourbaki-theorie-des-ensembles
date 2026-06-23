"""Tests — PROPOSITION 2 §III.5.2 (E III.36) : a < b ⟺ ∃c>0, b=a+c."""
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop2_strict_iii5 import (
    prop2_strict_forward, prop2_strict_backward,
    prop2_strict_equivalence, prop2_strict_equivalence_enonce,
)
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.logique.formule import (
    var, egal, non, et, impl, existe, equiv,
)
from bourbaki.cardinaux.ensembles_cardinaux import inf_strict_card
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_entier, ZERO
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_cardinale_binaire


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22


def test_forward_clos():
    t = prop2_strict_forward()
    assert t.est_clos and not t.hypotheses


def test_backward_clos():
    t = prop2_strict_backward()
    assert t.est_clos and not t.hypotheses


def test_equivalence_close_et_enonce():
    t = prop2_strict_equivalence()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == prop2_strict_equivalence_enonce()


def test_enonce_forme_exacte():
    a, b, c = var("aP2"), var("bP2"), "cP2"
    vc = var(c)
    rhs = existe(c, et(est_entier(vc), et(non(egal(vc, ZERO)),
                                          egal(b, somme_cardinale_binaire(a, vc)))))
    attendu = impl(et(est_entier(a), est_entier(b)),
                   equiv(inf_strict_card(a, b), rhs))
    assert prop2_strict_equivalence_enonce() == attendu


def test_pas_tautologie():
    # la conclusion n'est pas dans les hypothèses (énoncé non vacuous)
    t = prop2_strict_equivalence()
    assert t.conclusion not in t.hypotheses
