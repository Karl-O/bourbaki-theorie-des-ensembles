# -*- coding: utf-8 -*-
"""Tests §II.1.6 — forme de l'énoncé C51 (E II.5)."""
from bourbaki.i_description_mathematique_formelle.assemblage import (
    Assemblage, conjonction, existe, pour_tout, equivalence)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.theorie_ensembles import (
    appartient)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_collectivisantes.ensembles_selection_c51_c52 import (
    enonce_c51)


def test_enonce_c51_forme():
    """Coll_x(P et x∈A) = (∃Y)(∀x)((x∈Y) ⇔ (P et x∈A)), construit à la main."""
    P, A = Assemblage(("P",)), Assemblage(("A",))
    x, Y = Assemblage(("x",)), Assemblage(("Y",))
    attendu = existe("Y", pour_tout("x", equivalence(
        appartient(x, Y), conjonction(P, appartient(x, A)))))
    assert enonce_c51(P, A) == attendu
