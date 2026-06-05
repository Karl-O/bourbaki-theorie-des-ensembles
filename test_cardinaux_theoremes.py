"""Tests §III.3 — Eq(X,Card X) et Proposition 1 (sens direct)."""
from formule import var, egal, impl
import ensembles_abrege as E
from ensembles_cardinaux import equipotent, cardinal
from ensembles_cardinaux_theoremes import equipotent_son_cardinal, cardinal_egal_si_equipotent


def test_equipotent_son_cardinal():
    vX = var("X")
    t = equipotent_son_cardinal("X")
    assert t.conclusion == equipotent(vX, cardinal(vX)) and t.est_clos


def test_cardinal_egal_si_equipotent():
    vX, vY = var("X"), var("Y")
    t = cardinal_egal_si_equipotent("X", "Y")
    assert t.conclusion == impl(equipotent(vX, vY), egal(cardinal(vX), cardinal(vY)))
    assert t.est_clos


def test_equipotent_si_cardinal_egal():
    from ensembles_cardinaux_theoremes import equipotent_si_cardinal_egal
    vX, vY = var("X"), var("Y")
    t = equipotent_si_cardinal_egal("X", "Y")
    assert t.conclusion == impl(egal(cardinal(vX), cardinal(vY)), equipotent(vX, vY))
    assert t.est_clos


def test_proposition_1_cardinaux():
    from formule import equiv
    from ensembles_cardinaux_theoremes import proposition_1_cardinaux
    vX, vY = var("X"), var("Y")
    t = proposition_1_cardinaux("X", "Y")
    assert t.conclusion == equiv(equipotent(vX, vY), egal(cardinal(vX), cardinal(vY)))
    assert t.est_clos


def test_inf_egal_reflexif():
    from ensembles_cardinaux import inf_egal_card
    from ensembles_cardinaux_theoremes import inf_egal_reflexif, cardinal_inf_egal_reflexif
    vX = var("X")
    assert inf_egal_reflexif("X").conclusion == inf_egal_card(vX, vX)
    assert inf_egal_reflexif("X").est_clos
    c = cardinal_inf_egal_reflexif("X")
    assert c.conclusion == inf_egal_card(cardinal(vX), cardinal(vX)) and c.est_clos
