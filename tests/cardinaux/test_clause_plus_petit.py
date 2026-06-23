"""Tests MIROIR — clause_plus_petit(≤,[0,a]) (bottleneck ordinal↔cardinal, arc ℕ).

Couvre les trois modules NEUFS :
  • ensembles_clause_plus_petit_monotonie  : inf_egal_card_de_inclus (PIVOT brut).
  • ensembles_clause_plus_petit_correspondance : card_le_de_seg_inclus (PIVOT littéral).
  • ensembles_clause_plus_petit             : réduction vers cardinaux_bien_ordonnes(a).

INVARIANT vérifié : theorie_ensembles() = 22 ; aucune tautologie vide ; les pièces
ordinales reportées sont les SEULES hypothèses résiduelles.
"""
from bourbaki.logique.formule import (
    var, inclus, impl, egal, et, appartient, existe, pourtout,
)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal

import bourbaki.cardinaux.ensembles_clause_plus_petit_monotonie as MONO
import bourbaki.cardinaux.ensembles_clause_plus_petit_correspondance as CORR
import bourbaki.cardinaux.ensembles_clause_plus_petit as CPP
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinaux_bien_ordonnes


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  BRIQUE 1 — inf_egal_card_de_inclus : A⊂B ⇒ A≤B  (INCONDITIONNEL, NON vacueux)
# ─────────────────────────────────────────────────────────────────────────────
def test_inf_egal_card_de_inclus_clos():
    t = MONO.inf_egal_card_de_inclus("A", "B")
    assert t.est_clos
    assert not t.hypotheses
    expected = impl(inclus(var("A"), var("B")), inf_egal_card(var("A"), var("B")))
    assert t.conclusion == expected
    # NON vacueux : la conclusion n'est PAS A⊂B⇒A⊂B
    assert t.conclusion != impl(inclus(var("A"), var("B")), inclus(var("A"), var("B")))


def test_inf_egal_card_de_inclus_terme_clos():
    A, B = var("A"), var("B")
    t = MONO.inf_egal_card_de_inclus_terme(A, B)
    assert t.est_clos
    assert t.conclusion == impl(inclus(A, B), inf_egal_card(A, B))


# ─────────────────────────────────────────────────────────────────────────────
#  BRIQUE 2 — card_le_de_seg_inclus : pivot monotone LITTÉRAL m≤x.
# ─────────────────────────────────────────────────────────────────────────────
def test_card_le_de_seg_inclus():
    a, R, m, x = var("a"), var("R"), var("m"), var("x")
    t = CORR.card_le_de_seg_inclus(a, R, m, x)
    # conclusion == m ≤ x  (la cible MONOTONE)
    assert t.conclusion == inf_egal_card(m, x)
    # hypothèses EXACTES : seg_m⊂seg_x, Card seg_m=m, Card seg_x=x
    sm, sx = CORR.seg_terme(a, R, m), CORR.seg_terme(a, R, x)
    expected = {inclus(sm, sx), egal(cardinal(sm), m), egal(cardinal(sx), x)}
    assert set(t.hypotheses) == expected
    # NON vacueux : conclusion ≠ une des hypothèses
    assert t.conclusion not in t.hypotheses


def test_seg_inclus_donne_card_le_clos():
    a, R, m, x = var("a"), var("R"), var("m"), var("x")
    t = CORR.seg_inclus_donne_card_le(a, R, m, x)
    assert t.est_clos
    sm, sx = CORR.seg_terme(a, R, m), CORR.seg_terme(a, R, x)
    assert t.conclusion == impl(inclus(sm, sx), inf_egal_card(sm, sx))


# ─────────────────────────────────────────────────────────────────────────────
#  ÉTAPE B — plus_petit_de_segments : (∃m)(m∈S et (∀x∈S)m≤x) sous 2 hyps ordinales.
# ─────────────────────────────────────────────────────────────────────────────
def test_plus_petit_de_segments():
    a, R, S, m, x = var("a"), var("R"), var("S"), var("m"), var("x")
    t = CPP.plus_petit_de_segments(a, R, S, m, x)
    concl = existe("m", et(appartient(m, S),
        pourtout("x", impl(appartient(x, S), inf_egal_card(m, x)))))
    assert t.conclusion == concl
    expected = {CORR.hyp_surjection(a, R, S, "xs"),
                CORR.hyp_bon_ordre_seg(a, R, S, "ms", "xs")}
    assert set(t.hypotheses) == expected


# ─────────────────────────────────────────────────────────────────────────────
#  ÉTAPE C — cardinaux_bien_ordonnes_de_segments : == cardinaux_bien_ordonnes(a) (C61).
# ─────────────────────────────────────────────────────────────────────────────
def test_cardinaux_bien_ordonnes_de_segments_match_C61():
    a = var("a")
    t = CPP.cardinaux_bien_ordonnes_de_segments(a)
    # 🎯 conclusion == la CIBLE C61 LITTÉRALEMENT
    assert t.conclusion == cardinaux_bien_ordonnes(a)
    # SEULES hypothèses : les deux pièces ordinales QUANTIFIÉES sur S
    expected = {CPP.hyp_surjection_tous_S(a), CPP.hyp_bon_ordre_seg_tous_S(a)}
    assert set(t.hypotheses) == expected
    # NON vacueux : la cible n'est aucune des hypothèses
    assert t.conclusion not in t.hypotheses


# ─────────────────────────────────────────────────────────────────────────────
#  COHÉRENCE — les deux hyps « tous_S » sont bien des (∀S) des pièces ordinales.
# ─────────────────────────────────────────────────────────────────────────────
def test_hyps_tous_S_forme():
    a, S = var("a"), var("S")
    assert CPP.hyp_surjection_tous_S(a) == pourtout("S", CORR.hyp_surjection(a, "R", S, "xs"))
    assert CPP.hyp_bon_ordre_seg_tous_S(a) == pourtout("S", CORR.hyp_bon_ordre_seg(a, "R", S, "ms", "xs"))
