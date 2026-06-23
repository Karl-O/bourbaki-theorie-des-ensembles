"""Tests MIROIR — ensembles_bon_ordre_intervalle_ordinal : LE TRANSPORT ordinal↔cardinal
vers le GATE ℕ `bon_ordre_intervalle(a)`.

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : aucune conclusion n'est l'une de ses hypothèses.
Hypothèses EXACTES contrôlées.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, appartient, inclus, egal, et, impl, non, pourtout, existe
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V

import bourbaki.cardinaux.iii_4_ordinal_cardinal.bon_ordre_intervalle.ensembles_bon_ordre_intervalle_ordinal as M
import bourbaki.cardinaux.iii_4_ordinal_cardinal.bon_ordre_intervalle.ensembles_ordinaux_bien_ordonnes as OBO
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import seg, _R_de
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.cardinaux.iii_4_ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_correspondance import (
    bon_ordre_intervalle, intervalle_0a,
)


def _Rf(R="Ro"):
    return _R_de(R)


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 PIÈCE 1 — iso_reflexif_seg_preuve : l'ISO IDENTITÉ (résout le report OBO).
# ─────────────────────────────────────────────────────────────────────────────
def test_iso_reflexif_seg_preuve_conclusion():
    t = M.iso_reflexif_seg_preuve("Ro", "o", "m")
    assert t.conclusion == M.iso_reflexif_seg_cible("Ro", "o", "m")


def test_iso_reflexif_seg_preuve_resout_le_report_OBO():
    # la conclusion est EXACTEMENT l'énoncé iso_reflexif_seg reporté par OBO.
    t = M.iso_reflexif_seg_preuve("Ro", "o", "m")
    assert t.conclusion == OBO.iso_reflexif_seg("Ro", "o", "m", f="fseg")


def test_iso_reflexif_seg_preuve_forme():
    t = M.iso_reflexif_seg_preuve("Ro", "o", "m")
    Rf = _Rf()
    Sm = seg("Ro", "o", var("m"))
    assert t.conclusion == V.sont_isomorphes_ordre(Sm, Sm, Rf, Rf, "fseg", "x", "w")


def test_iso_reflexif_seg_preuve_CLOS():
    t = M.iso_reflexif_seg_preuve("Ro", "o", "m")
    assert len(t.hypotheses) == 0          # INCONDITIONNEL (iso identité Δ construite)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 PIÈCE 2 — card_seg_monotone : seg⊂seg ⇒ Card seg ≤ Card seg (CLOS).
# ─────────────────────────────────────────────────────────────────────────────
def test_card_seg_monotone_conclusion_forme():
    t = M.card_seg_monotone("Ro", "o", "m", "x")
    Sm = seg("Ro", "o", var("m"))
    Sx = seg("Ro", "o", var("x"))
    expected = impl(inclus(Sm, Sx), inf_egal_card(cardinal(Sm), cardinal(Sx)))
    assert t.conclusion == expected


def test_card_seg_monotone_CLOS():
    t = M.card_seg_monotone("Ro", "o", "m", "x")
    assert len(t.hypotheses) == 0          # tout est dans l'implication déchargée
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 PIÈCE 3 — plus_petit_card_segment : ≤-MIN des cardinaux de segments.
# ─────────────────────────────────────────────────────────────────────────────
def test_plus_petit_card_segment_conclusion():
    t = M.plus_petit_card_segment("Ro", "a", "T")
    assert t.conclusion == M.plus_petit_card_segment_cible("Ro", "a", "T")


def test_plus_petit_card_segment_conclusion_forme():
    t = M.plus_petit_card_segment("Ro", "a", "T")
    vT = var("T")
    vm, vx = var("ms"), var("xs")
    expected = existe("ms", et(appartient(vm, vT),
        pourtout("xs", impl(appartient(vx, vT),
            inf_egal_card(cardinal(seg("Ro", "a", vm)), cardinal(seg("Ro", "a", vx)))))))
    assert t.conclusion == expected


def test_plus_petit_card_segment_hypotheses_exactes():
    t = M.plus_petit_card_segment("Ro", "a", "T")
    Rf = _Rf()
    exp = {
        E.est_bien_ordonne(Rf, var("a"), "x", "y", "z", "T", "ms", "xs"),  # bon ordre de a
        inclus(var("T"), var("a")),                                        # T ⊂ a
        non(egal(var("T"), E.VIDE)),                                        # T ≠ ∅
    }
    assert set(t.hypotheses) == exp


def test_plus_petit_card_segment_non_vacueux():
    t = M.plus_petit_card_segment("Ro", "a", "T")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  PIÈCE 4 — clause_min_intervalle_de_pullback : transport ⊆-min → ≤-min de S.
# ─────────────────────────────────────────────────────────────────────────────
def test_clause_min_pullback_hypotheses_exactes():
    t = M.clause_min_intervalle_de_pullback("Ro", "a", "S", "T")
    Rf = _Rf()
    exp = {
        E.est_bien_ordonne(Rf, var("a"), "x", "y", "z", "T", "ms", "xs"),  # bon ordre de a
        inclus(var("T"), var("a")),                                        # T ⊂ a
        non(egal(var("T"), E.VIDE)),                                        # T ≠ ∅
        inclus(var("S"), intervalle_0a("a")),                              # S ⊂ [0,a]
        M.hyp_realisation_min("Ro", "a", "S", "T"),                        # into
        M.hyp_realisation_onto("Ro", "a", "S", "T"),                       # onto
    }
    assert set(t.hypotheses) == exp


def test_clause_min_pullback_non_vacueux():
    t = M.clause_min_intervalle_de_pullback("Ro", "a", "S", "T")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 PIÈCE 5 — bon_ordre_intervalle_ordinal(a) ⊢ bon_ordre_intervalle(a).
#  LE GATE ℕ : conclusion == cible déposée, 1 SEULE hypothèse (hyp_transport_ordinal).
# ─────────────────────────────────────────────────────────────────────────────
def test_bon_ordre_intervalle_ordinal_conclusion_EST_LA_CIBLE():
    t = M.bon_ordre_intervalle_ordinal("a")
    assert t.conclusion == bon_ordre_intervalle("a")          # == la cible DÉPOSÉE


def test_bon_ordre_intervalle_ordinal_une_seule_hypothese():
    t = M.bon_ordre_intervalle_ordinal("a")
    assert set(t.hypotheses) == {M.hyp_transport_ordinal("a")}   # le SEUL report


def test_bon_ordre_intervalle_ordinal_non_vacueux():
    t = M.bon_ordre_intervalle_ordinal("a")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


def test_hyp_transport_ordinal_est_un_existe_Ro():
    # le report est bien un (∃Ro)(...) — pas une tautologie déguisée.
    h = M.hyp_transport_ordinal("a")
    assert h.tag == "exists" and h.lieur == "Ro"


def test_hyp_transport_ordinal_distinct_de_la_cible():
    # le report N'EST PAS la cible (sinon vacuité).
    assert M.hyp_transport_ordinal("a") != bon_ordre_intervalle("a")
