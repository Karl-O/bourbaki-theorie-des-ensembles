"""Tests — bornes exponentielles INCONDITIONNELLES (E.III.3.5).

B1  base_inf_egal_exposant  ⊢ (b≠0) ⇒ (Card a ≤ a^b)
B2  un_inf_egal_exposant    ⊢ (a≠0) ⇒ (1 ≤ a^b),  1 = Card{∅}
"""
from bourbaki.logique.formule import var, egal, non, impl
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)
from bourbaki.cardinaux.ensembles_bornes_exposant import (
    support_base_exposant, base_inf_egal_exposant, un_inf_egal_exposant)

UN = E.singleton(E.VIDE)          # 1 = Card{∅} (la valeur SET)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_support_base_clos():
    t = support_base_exposant("B", "A")
    assert t.est_clos and len(t.hypotheses) == 0


def test_B1_base_inf_egal_exposant_clean():
    a, b = var("a"), var("b")
    t = base_inf_egal_exposant("a", "b")
    assert t.est_clos and len(t.hypotheses) == 0
    clean = impl(non(egal(b, E.VIDE)),
                 inf_egal_card(cardinal(a), exposant_cardinal_binaire(a, b)))
    assert t.conclusion == clean


def test_B2_un_inf_egal_exposant_clean():
    a, b = var("a"), var("b")
    t = un_inf_egal_exposant("a", "b")
    assert t.est_clos and len(t.hypotheses) == 0
    clean = impl(non(egal(a, E.VIDE)),
                 inf_egal_card(cardinal(UN), exposant_cardinal_binaire(a, b)))
    assert t.conclusion == clean
