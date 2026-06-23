"""Tests §III.3 Prop 10 Cor 2 : (∏a_ι)^b = ∏ a_ι^b (forme ensembliste + réduction)."""
from bourbaki.logique.formule import impl, egal
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.ensembles_prop10cor2_iii3 import (
    membre_source, membre_but, source, but,
    eq_source_son_cardinal, eq_but_son_cardinal,
    cor2_via_eq,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_membre_source_clos():
    th = membre_source()
    assert th.est_clos


def test_membre_but_clos():
    th = membre_but()
    assert th.est_clos


def test_eq_source_son_cardinal_clos():
    assert eq_source_son_cardinal().est_clos


def test_eq_but_son_cardinal_clos():
    assert eq_but_son_cardinal().est_clos


def test_cor2_via_eq_clos_et_exact():
    """Eq(source,but) ⇒ Card(source)=Card(but) : CLOS, 0 hyp, conclusion EXACTE."""
    th = cor2_via_eq()
    assert th.est_clos
    src, tgt = source(), but()
    cible = impl(equipotent(src, tgt), egal(cardinal(src), cardinal(tgt)))
    assert th.conclusion == cible
