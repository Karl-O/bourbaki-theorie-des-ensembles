"""Tests — eq_exposant_invariant : Eq(X,Y) ⇒ Eq(𝓕(X;A), 𝓕(Y;A))."""
from bourbaki.logique.i_1_termes_relations.formule import var, impl
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import equipotent
from bourbaki.cardinaux.ensembles_eq_exposant_invariant import (
    eq_exposant_invariant, injection_via_pointmap, _source, _but)
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles


def _cible(x, y, a):
    return impl(equipotent(var(x), var(y)),
                equipotent(E.applications(var(x), var(a)),
                           E.applications(var(y), var(a))))


def test_eq_exposant_invariant_clos():
    th = eq_exposant_invariant("X", "Y", "a")
    assert th.est_clos is True
    assert list(th.hypotheses) == []


def test_eq_exposant_invariant_conclusion():
    th = eq_exposant_invariant("X", "Y", "a")
    assert th.conclusion == _cible("X", "Y", "a")


def test_eq_exposant_invariant_defaut():
    th = eq_exposant_invariant()
    assert th.est_clos is True and not th.hypotheses
    assert th.conclusion == _cible("X", "Y", "a")


def test_eq_exposant_invariant_a_egal_A():
    th = eq_exposant_invariant("X", "Y", "A")
    assert th.est_clos is True and not th.hypotheses
    assert th.conclusion == _cible("X", "Y", "A")


def test_builder_generique_sous_bijection():
    # {est_bijection_de(m,T,S)} ⊢ inf_egal_card(𝓕(S;A), 𝓕(T;A))
    th = injection_via_pointmap(var("S"), var("T"), var("m"))
    assert th.conclusion == inf_egal_card(_source(var("S")), _but(var("T")))
    assert len(th.hypotheses) == 1   # uniquement la bijection-pointmap


def test_theorie_inchangee_22_axiomes():
    assert len(theorie_ensembles().axiomes) == 22
