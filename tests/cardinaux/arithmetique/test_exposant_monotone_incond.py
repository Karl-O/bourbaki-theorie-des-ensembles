"""Tests — monotonie INCONDITIONNELLE de l'exponentiation (§III.3.5).

M1 (base) : (a ≤ b) ⇒ (a^c ≤ b^c), sans aucune hypothèse de support.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, impl
import bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, est_injection_de
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire
from bourbaki.cardinaux.arithmetique.ensembles_exposant_monotone_incond import (
    injection_post_composition, support_monotone_base, exposant_monotone_base)


def test_injection_post_composition_sous_injection():
    # {est_injection_de(ι,A,B)} ⊢ inf_egal_card(𝓕(C;A), 𝓕(C;B))
    th = injection_post_composition("A", "B", "C", "iota")
    src = E.applications(var("C"), var("A"))
    cod = E.applications(var("C"), var("B"))
    assert th.conclusion == inf_egal_card(src, cod)
    assert list(th.hypotheses) == [est_injection_de(var("iota"), var("A"), var("B"))]


def test_support_monotone_base_clos():
    th = support_monotone_base("A", "B", "C")
    assert th.est_clos is True
    assert list(th.hypotheses) == []
    src = E.applications(var("C"), var("A"))
    cod = E.applications(var("C"), var("B"))
    assert th.conclusion == impl(inf_egal_card(var("A"), var("B")),
                                 inf_egal_card(src, cod))


def test_exposant_monotone_base_CLEAN():
    th = exposant_monotone_base("a", "b", "c")
    assert th.est_clos is True
    assert list(th.hypotheses) == []
    a, b, c = var("a"), var("b"), var("c")
    cible = impl(inf_egal_card(a, b),
                 inf_egal_card(exposant_cardinal_binaire(a, c),
                               exposant_cardinal_binaire(b, c)))
    assert th.conclusion == cible


def test_theorie_inchangee_22():
    assert len(theorie_ensembles().axiomes) == 22
