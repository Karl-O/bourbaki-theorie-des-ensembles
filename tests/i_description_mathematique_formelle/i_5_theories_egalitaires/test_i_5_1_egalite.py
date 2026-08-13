# -*- coding: utf-8 -*-
"""Tests §I.5 — l'assemblage T = U (E I.38)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import Assemblage
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_1_egalite import egalite


def test_egalite_prefixe():
    t, u = Assemblage(("x",)), Assemblage(("y",))
    assert egalite(t, u).signes == ("=", "x", "y")
    assert egalite(t, u).liens == ()


def test_facade_compatible():
    from bourbaki.i_description_mathematique_formelle.assemblage import egalite as e2
    assert e2 is egalite
