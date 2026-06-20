"""Tests — Prop. 7 §III.5, fonction caractéristique (E III.39)."""
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire as prod,
)
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_cardinale_binaire as somme,
)
from bourbaki.logique.formule import var, egal
from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
from bourbaki.entiers.ensembles_prop7_caracteristique_iii5 import (
    carac_intersection, carac_complement, carac_union, phi,
)


def _peler(th):
    """Pèle TOUS les antécédents d'une cascade d'implications ⇒ (consequent final)."""
    c = th.conclusion
    ants = []
    while c.tag == "ou":
        try:
            a, c = antecedent_consequent(c)
        except Exception:
            break
        ants.append(a)
    return ants, c


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_carac_intersection_close():
    th = carac_intersection()
    assert th.est_clos and len(th.hypotheses) == 0
    ants, cons = _peler(th)
    vx, vA, vB, vE = var("x"), var("A"), var("B"), var("E")
    AB = E.intersection(vA, vB)
    expected = egal(phi(AB, vE, vx), prod(phi(vA, vE, vx), phi(vB, vE, vx)))
    assert cons == expected
    # honnêteté : la conclusion n'est PAS parmi les hypothèses (H)
    assert expected not in ants


def test_carac_complement_close():
    th = carac_complement()
    assert th.est_clos and len(th.hypotheses) == 0
    ants, cons = _peler(th)
    vx, vA, vE = var("x"), var("A"), var("E")
    cA = E.difference(vE, vA)
    expected = egal(somme(phi(cA, vE, vx), phi(vA, vE, vx)), UN_CARD())
    assert cons == expected
    assert expected not in ants


def test_carac_union_close():
    th = carac_union()
    assert th.est_clos and len(th.hypotheses) == 0
    ants, cons = _peler(th)
    vx, vA, vB, vE = var("x"), var("A"), var("B"), var("E")
    AB = E.intersection(vA, vB)
    AuB = E.reunion(vA, vB)
    lhs = somme(phi(AuB, vE, vx), phi(AB, vE, vx))
    rhs = somme(phi(vA, vE, vx), phi(vB, vE, vx))
    expected = egal(lhs, rhs)
    assert cons == expected
    assert expected not in ants


def UN_CARD():
    from bourbaki.entiers.ensembles_entiers import UN
    return UN
