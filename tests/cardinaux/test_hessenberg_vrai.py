"""Tests — Hessenberg NON-VACUEUX (`ensembles_hessenberg_vrai`).

Vérifie que `negation_b_inf_strict_a_vrai` est CLOS, theorie=22, et — surtout —
NON-VACUEUX : le trio géométrique contradictoire (S₀∪U=S₀, u∈U, U∩S₀=∅) n'est PLUS
présent dans l'ensemble des hypothèses (les deux faits dangereux sont DÉRIVÉS).
"""
from bourbaki.logique.formule import (
    var, egal, non, impl, pourtout, appartient, inclus, tau,
)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal

from bourbaki.cardinaux.ensembles_hessenberg_vrai import (
    realiser_U, U_disjoint_derive, U_non_vide_derive, u_dans_U_derive,
    negation_b_inf_strict_a_vrai, negation_b_inf_strict_a_vrai_cible,
    _temoin_U, _temoin_u,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_realiser_U_clos():
    r = realiser_U("E", "S0")
    Ut, corps, _ = _temoin_U("E", "S0")
    assert r.conclusion == corps
    assert r.conclusion not in r.hypotheses


def test_u_disjoint_derive():
    d = U_disjoint_derive("E", "S0")
    Ut, _, _ = _temoin_U("E", "S0")
    cible = pourtout("z", impl(appartient(var("z"), Ut),
                               non(appartient(var("z"), var("S0")))))
    assert d.conclusion == cible


def test_u_non_vide_derive():
    n = U_non_vide_derive("E", "S0")
    Ut, _, _ = _temoin_U("E", "S0")
    assert n.conclusion == non(egal(Ut, E.VIDE))


def test_u_dans_U_derive():
    u = u_dans_U_derive("E", "S0")
    Ut, _, _ = _temoin_U("E", "S0")
    ut = _temoin_u(Ut)
    assert u.conclusion == appartient(ut, Ut)


def test_negation_vrai_clos_et_non_vacueux():
    r = negation_b_inf_strict_a_vrai("E", "S0")
    assert r.conclusion == negation_b_inf_strict_a_vrai_cible("E", "S0")
    assert r.conclusion not in r.hypotheses
    # 𝔟<a déchargée
    lt_hyps = [h for h in r.hypotheses
               if getattr(h, "lieur", None) == "" and h == _lt()]
    assert _lt() not in r.hypotheses
    # ANTI-VACUITÉ : le trio contradictoire est ABSENT
    Ut, _, _ = _temoin_U("E", "S0")
    ut = _temoin_u(Ut)
    trio_disj = pourtout("z", impl(appartient(var("z"), Ut),
                                   non(appartient(var("z"), var("S0")))))
    trio_u = appartient(ut, Ut)
    assert trio_disj not in r.hypotheses, "trio (U∩S₀=∅) réapparaît en hypothèse — VACUEUX"
    assert trio_u not in r.hypotheses, "trio (u∈U) réapparaît en hypothèse — VACUEUX"


def _lt():
    from bourbaki.cardinaux.ensembles_cardinaux import inf_strict_card
    return inf_strict_card(cardinal(var("S0")), cardinal(var("E")))
