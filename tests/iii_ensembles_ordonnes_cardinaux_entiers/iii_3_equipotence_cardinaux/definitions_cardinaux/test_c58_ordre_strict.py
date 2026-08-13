# -*- coding: utf-8 -*-
"""Tests §III.1.4 — C58 (E III.5) : partie 1 (équivalence) + partie 2 (transitivités mixtes)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, ou, egal, impl, equiv)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card, est_cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_c58_ordre_strict import (
    c58_enonce, c58_ordre_strict, c58_trans_gauche, c58_trans_droite)


def test_c58_clos():
    th = c58_ordre_strict()
    assert th.conclusion == c58_enonce()
    assert not th.hypotheses                      # CLOS : 0 hypothèse


def test_c58_enonce_est_l_equivalence_du_livre():
    vx, vy = var("x58"), var("y58")
    assert c58_enonce() == equiv(inf_egal_card(vx, vy),
                                 ou(inf_strict_card(vx, vy), egal(vx, vy)))


def test_c58_autres_lettres():
    th = c58_ordre_strict("a", "b")
    assert th.conclusion == c58_enonce("a", "b")
    assert not th.hypotheses


# ── Partie 2 : transitivités mixtes (E III.5 L.8-15) ──────────────────────────

def test_c58_trans_gauche():
    """{card(y),card(z)} ⊢ (x≤y et y<z) ⇒ x<z."""
    x, y, z = var("x58"), var("y58"), var("z58")
    th = c58_trans_gauche()
    assert th.conclusion == impl(et(inf_egal_card(x, y), inf_strict_card(y, z)),
                                 inf_strict_card(x, z))
    assert th.hypotheses == frozenset({est_cardinal(y), est_cardinal(z)})


def test_c58_trans_droite():
    """{card(x),card(y)} ⊢ (x<y et y≤z) ⇒ x<z."""
    x, y, z = var("x58"), var("y58"), var("z58")
    th = c58_trans_droite()
    assert th.conclusion == impl(et(inf_strict_card(x, y), inf_egal_card(y, z)),
                                 inf_strict_card(x, z))
    assert th.hypotheses == frozenset({est_cardinal(x), est_cardinal(y)})
