"""Tests — Prop 10 Direction A (INJECTION DE CURRY) : inf_egal_card(𝓕(B×C;A), 𝓕(C;𝓕(B;A)))."""
from bourbaki.cardinaux.arithmetique.ensembles_prop10_inj_curry import (
    W_Lambda_fonctionnel, W_Lambda_domaine, W_Lambda_image_incluse,
    W_Lambda_injective, W_Lambda_est_injection, inf_egal_curry,
)
from bourbaki.cardinaux.ensembles_cardinaux import est_injection_de, inf_egal_card
from bourbaki.cardinaux.arithmetique.ensembles_prop10_inj_curry import W_Lambda
from bourbaki.cardinaux.arithmetique.ensembles_prop10_currying import (
    domaine_lambda, codomaine_lambda)


def test_W_Lambda_fonctionnel_clos():
    th = W_Lambda_fonctionnel()
    assert th.est_clos


def test_W_Lambda_domaine_clos():
    th = W_Lambda_domaine()
    assert th.est_clos


def test_W_Lambda_image_incluse_clos():
    th = W_Lambda_image_incluse()
    assert th.est_clos


def test_W_Lambda_injective_clos():
    th = W_Lambda_injective()
    assert th.est_clos


def test_W_Lambda_est_injection_clos():
    th = W_Lambda_est_injection()
    assert th.est_clos
    assert th.conclusion == est_injection_de(
        W_Lambda(), domaine_lambda(), codomaine_lambda())


def test_inf_egal_curry_clos():
    th = inf_egal_curry()
    assert th.est_clos
    assert th.conclusion == inf_egal_card(domaine_lambda(), codomaine_lambda())
