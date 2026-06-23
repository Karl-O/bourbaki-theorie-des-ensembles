"""Tests — PROPOSITION 13 §III.3.6 ÉQUIVALENCE COMPLÈTE (a ≥ b ⟺ (∃c) a = b+c)."""
from bourbaki.cardinaux.ensembles_prop13_full_iii3 import (
    prop13_forward_card, prop13_forward_card_enonce,
    prop13_backward_card, prop13_backward_card_enonce,
    prop13_equivalence, prop13_equivalence_enonce,
)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles


def test_prop13_backward_card():
    t = prop13_backward_card()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == prop13_backward_card_enonce()


def test_prop13_forward_card():
    t = prop13_forward_card()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == prop13_forward_card_enonce()


def test_prop13_equivalence():
    t = prop13_equivalence()
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == prop13_equivalence_enonce()


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
