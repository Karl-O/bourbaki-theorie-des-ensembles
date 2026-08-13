"""Tests — eq_exposant_invariant : Eq(X,Y) ⇒ Eq(𝓕(X;A), 𝓕(Y;A))."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, impl
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import equipotent
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_eq_exposant_invariant import (
    eq_exposant_invariant, injection_via_pointmap, _source, _but)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles


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
