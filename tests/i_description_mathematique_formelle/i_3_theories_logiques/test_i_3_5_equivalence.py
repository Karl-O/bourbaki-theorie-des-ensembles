# -*- coding: utf-8 -*-
"""Tests §I.3.5 — « ⇔ » comme abréviation (E I.30)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, implication)
from bourbaki.i_description_mathematique_formelle.i_3_theories_logiques.i_3_4_conjonction import (
    conjonction)
from bourbaki.i_description_mathematique_formelle.i_3_theories_logiques.i_3_5_equivalence import (
    equivalence)

P, Q = Assemblage(("p",)), Assemblage(("q",))


def test_equivalence_est_l_abreviation():
    assert equivalence(P, Q) == conjonction(implication(P, Q), implication(Q, P))


def test_facade_compatible():
    from bourbaki.i_description_mathematique_formelle.assemblage import equivalence as e2
    assert e2 is equivalence
