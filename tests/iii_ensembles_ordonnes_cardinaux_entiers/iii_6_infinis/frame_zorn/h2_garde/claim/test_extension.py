# -*- coding: utf-8 -*-
"""Miroir de claim/ensembles_extension.py — étapes (2)+(3) de l'extension."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, existe, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.ensembles_extension import (
    b_le_complement, existe_u_cadre,
)


def test_b_le_complement():
    """{S₀⊂E, 𝔟+𝔟=𝔟, 𝔟<Card E} ⊢ 𝔟 ≤ Card(E∖S₀)."""
    vE, vS = var("E"), var("S0")
    t = b_le_complement("E", "S0")
    assert t.conclusion == inf_egal_card(
        cardinal(vS), cardinal(E.difference(vE, vS)))
    assert len(t.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22


def test_existe_u_cadre():
    """… ⊢ (∃Ucadre)(Ucadre ⊂ E∖S₀ et Card Ucadre = 𝔟)."""
    vE, vS = var("E"), var("S0")
    R = E.difference(vE, vS)
    t = existe_u_cadre("E", "S0")
    assert t.conclusion == existe("Ucadre", et(
        inclus(var("Ucadre"), R), egal(cardinal(var("Ucadre")), cardinal(vS))))
    assert t.conclusion not in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
