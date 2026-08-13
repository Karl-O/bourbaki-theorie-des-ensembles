"""Tests MIROIR — ensembles_segments_construction : MONOTONIE INCONDITIONNELLE des
VRAIS segments initiaux d'un ensemble bien ordonné (segment_extremite), pour fermer
seg_monotone de l'arc cardinaux_bien_ordonnes → C61 → ℕ.

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : la conclusion seg(t)⊂seg(t') (et la forme ∀ seg_monotone) n'est
JAMAIS l'une des hypothèses.  Hypothèses EXACTES contrôlées.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient, inclus, egal, et, impl, non, pourtout, libres_f,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction as SC
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal


def _Rf():
    return lambda x, y: appartient(E.couple(x, y), var("R"))


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  membre_segment — caractérisation de l'appartenance (axiome instancié), CLOS.
# ─────────────────────────────────────────────────────────────────────────────
def test_membre_segment_clos():
    m = SC.membre_segment("R", "a", "t", "u")
    assert m.est_clos
    assert not m.hypotheses
    # équivalence u∈seg ⇔ ((u∈a et R{u,t}) et u≠t) : tête = équivalence (¬∃ encodée)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 seg_strict_monotone — LE COEUR : seg(t) ⊂ seg(t') sous {transitif, antisym, R{t,s}}.
# ─────────────────────────────────────────────────────────────────────────────
def test_seg_strict_monotone_conclusion():
    t = SC.seg_strict_monotone("R", "a", "t", "s")
    St = SC.seg("R", "a", "t")
    Ss = SC.seg("R", "a", "s")
    assert t.conclusion == inclus(St, Ss)


def test_seg_strict_monotone_hypotheses_exactes():
    t = SC.seg_strict_monotone("R", "a", "t", "s")
    Rf = _Rf()
    exp = {
        Rf(var("t"), var("s")),                 # R{t,s}
        E.ordre_transitif(Rf),                  # transitivité
        E.ordre_antisymetrique(Rf),             # antisymétrie
    }
    assert set(t.hypotheses) == exp


def test_seg_strict_monotone_non_vacueux():
    t = SC.seg_strict_monotone("R", "a", "t", "s")
    # la conclusion n'est aucune des hypothèses (pas de tautologie / affaibli)
    assert t.conclusion not in set(t.hypotheses)


def test_seg_strict_monotone_theorie_22():
    SC.seg_strict_monotone("R", "a", "t", "s")
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 seg_monotone_reel — la pièce (2) LITTÉRALE pour les vrais segments,
#  conditionnée aux SEULES transitivité + antisymétrie.
# ─────────────────────────────────────────────────────────────────────────────
def test_seg_monotone_reel_forme_litterale():
    t = SC.seg_monotone_reel("R", "a", "S")
    Rf = _Rf()
    vS = var("S")
    vu, vv = var("us"), var("vs")
    St = SC.seg("R", "a", vu)
    Sv = SC.seg("R", "a", vv)
    expected = pourtout("us", pourtout("vs",
        impl(et(appartient(vu, vS), appartient(vv, vS)),
             impl(Rf(vu, vv), inclus(St, Sv)))))
    assert t.conclusion == expected


def test_seg_monotone_reel_hypotheses_exactes():
    t = SC.seg_monotone_reel("R", "a", "S")
    Rf = _Rf()
    assert set(t.hypotheses) == {E.ordre_transitif(Rf), E.ordre_antisymetrique(Rf)}


def test_seg_monotone_reel_non_vacueux():
    t = SC.seg_monotone_reel("R", "a", "S")
    assert t.conclusion not in set(t.hypotheses)


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 seg_monotone_de_bon_ordre — DÉCHARGÉ sur le SEUL bon ordre (a,R) (Zermelo).
# ─────────────────────────────────────────────────────────────────────────────
def test_seg_monotone_de_bon_ordre_hypothese_unique():
    t = SC.seg_monotone_de_bon_ordre("R", "a", "S")
    Rf = _Rf()
    assert set(t.hypotheses) == {E.est_bien_ordonne(Rf, var("a"))}


def test_seg_monotone_de_bon_ordre_meme_conclusion():
    # même conclusion littérale que seg_monotone_reel
    t1 = SC.seg_monotone_de_bon_ordre("R", "a", "S")
    t2 = SC.seg_monotone_reel("R", "a", "S")
    assert t1.conclusion == t2.conclusion


def test_seg_monotone_de_bon_ordre_non_vacueux():
    t = SC.seg_monotone_de_bon_ordre("R", "a", "S")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 hyp_bon_ordre_seg_reel — ⊂-MIN des segments réels, sous le SEUL bon ordre.
# ─────────────────────────────────────────────────────────────────────────────
def test_hyp_bon_ordre_seg_reel_conclusion():
    t = SC.hyp_bon_ordre_seg_reel("R", "a", "S")
    assert t.conclusion == SC.hyp_bon_ordre_seg_reel_cible("R", "a", "S")


def test_hyp_bon_ordre_seg_reel_hypotheses_exactes():
    t = SC.hyp_bon_ordre_seg_reel("R", "a", "S")
    Rf = _Rf()
    exp = {
        E.est_bien_ordonne(Rf, var("a"), "x", "y", "z", "S", "ms", "xs"),  # bon ordre de a
        inclus(var("S"), var("a")),                                        # S ⊂ a
        non(egal(var("S"), E.VIDE)),                                        # S ≠ ∅
    }
    assert set(t.hypotheses) == exp


def test_hyp_bon_ordre_seg_reel_non_vacueux():
    t = SC.hyp_bon_ordre_seg_reel("R", "a", "S")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  report_surjection_construction — l'énoncé de la SEULE pièce restante (report).
# ─────────────────────────────────────────────────────────────────────────────
def test_report_surjection_construction_forme():
    rs = SC.report_surjection_construction("R", "a", "S")
    vS = var("S")
    vt = var("ts")
    expected = pourtout("ts", impl(appartient(vt, vS),
                                   egal(cardinal(SC.seg("R", "a", vt)), vt)))
    assert rs == expected
