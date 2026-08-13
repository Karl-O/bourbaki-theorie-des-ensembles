# -*- coding: utf-8 -*-
"""Test §III.5.6 Th.1 — UNICITÉ du quotient et du reste de la division euclidienne.

_gap → _lt_chain → _unicite (route SANS commutativité, via prop4_translation_stricte).
« CLOS modulo C61 » ; theorie == 22 ; aucun postulat."""
import pytest
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_unicite import (
    _gap, enonce_gap, _lt_chain, enonce_lt_chain, _unicite, enonce_unicite)

pytestmark = pytest.mark.slow


def test_gap():
    """⊢ {card q, card q', fini q} (q<q') ⇒ (succ q ≤ q')."""
    r = _gap()
    assert r.conclusion == enonce_gap()
    assert len(r.hypotheses) == 3


def test_lt_chain():
    """⊢ {Fini b,q,q',r ; q<q' ; r<b} b·q+r < b·q'+r'  (le cœur, sans commutativité)."""
    r = _lt_chain()
    assert r.conclusion == enonce_lt_chain()
    assert len(r.hypotheses) == 6


def test_unicite():
    """⊢ {Fini b,q,q',r,r', +C61} (b·q+r=a et r<b et b·q'+r'=a et r'<b) ⇒ (q=q' et r=r')."""
    r = _unicite()
    assert r.conclusion == enonce_unicite()


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
