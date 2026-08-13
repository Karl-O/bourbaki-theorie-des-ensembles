# -*- coding: utf-8 -*-
"""Tests §I.3.4 — « et » comme abréviation (E I.29)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, negation, disjonction)
from bourbaki.i_description_mathematique_formelle.i_3_theories_logiques.i_3_4_conjonction import (
    conjonction)

P, Q = Assemblage(("p",)), Assemblage(("q",))


def test_conjonction_est_l_abreviation():
    assert conjonction(P, Q) == negation(disjonction(negation(P), negation(Q)))


def test_facade_compatible():
    from bourbaki.i_description_mathematique_formelle.assemblage import conjonction as c2
    assert c2 is conjonction
