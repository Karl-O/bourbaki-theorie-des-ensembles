"""Tests MIROIR — ensembles_ordinaux_bien_ordonnes : BON ORDRE de la classe des
ordinaux ≤ o (route ORDINALE vers ℕ, gate bon_ordre_intervalle).

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : aucune conclusion n'est l'une de ses hypothèses.
Hypothèses EXACTES contrôlées.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient, inclus, egal, et, impl, non, pourtout, existe,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.bon_ordre_intervalle.ensembles_ordinaux_bien_ordonnes as OBO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import seg, _R_de


def _Rf(R="Ro"):
    return _R_de(R)


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯🎯 ordinaux_bien_ordonnes — plus petit ordinal de T (⊂-min des segments).
# ─────────────────────────────────────────────────────────────────────────────
def test_ordinaux_bien_ordonnes_conclusion():
    t = OBO.ordinaux_bien_ordonnes("o", "Ro", "T")
    assert t.conclusion == OBO.ordinaux_bien_ordonnes_cible("o", "Ro", "T")


def test_ordinaux_bien_ordonnes_conclusion_forme():
    # (∃m)( m∈T et (∀x)( x∈T ⇒ seg(o,Ro,m) ⊂ seg(o,Ro,x) ) )
    t = OBO.ordinaux_bien_ordonnes("o", "Ro", "T")
    vT = var("T")
    vm, vx = var("ms"), var("xs")
    expected = existe("ms", et(appartient(vm, vT),
        pourtout("xs", impl(appartient(vx, vT),
                            inclus(seg("Ro", "o", vm), seg("Ro", "o", vx))))))
    assert t.conclusion == expected


def test_ordinaux_bien_ordonnes_hypotheses_exactes():
    t = OBO.ordinaux_bien_ordonnes("o", "Ro", "T")
    Rf = _Rf()
    exp = {
        E.est_bien_ordonne(Rf, var("o"), "x", "y", "z", "T", "ms", "xs"),  # bon ordre de o
        inclus(var("T"), var("o")),                                        # T ⊂ o
        non(egal(var("T"), E.VIDE)),                                        # T ≠ ∅
    }
    assert set(t.hypotheses) == exp


def test_ordinaux_bien_ordonnes_non_vacueux():
    t = OBO.ordinaux_bien_ordonnes("o", "Ro", "T")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 seg_est_segment_de_seg — le représentant du plus petit est un SEGMENT de
#  tout autre (moitié NON-ISO de ordinal_inferieur_ou_egal).  NOUVEAU, CLOS.
# ─────────────────────────────────────────────────────────────────────────────
def test_seg_est_segment_de_seg_conclusion():
    s = OBO.seg_est_segment_de_seg("Ro", "o", "m", "x")
    assert s.conclusion == OBO.seg_est_segment_de_seg_cible("Ro", "o", "m", "x")


def test_seg_est_segment_de_seg_conclusion_forme():
    s = OBO.seg_est_segment_de_seg("Ro", "o", "m", "x")
    Rf = _Rf()
    expected = E.est_segment(seg("Ro", "o", var("m")), Rf,
                             seg("Ro", "o", var("x")), "u", "v")
    assert s.conclusion == expected


def test_seg_est_segment_de_seg_hypotheses_exactes():
    s = OBO.seg_est_segment_de_seg("Ro", "o", "m", "x")
    Rf = _Rf()
    exp = {
        E.est_bien_ordonne(Rf, var("o")),                              # bon ordre de o
        inclus(seg("Ro", "o", var("m")), seg("Ro", "o", var("x"))),    # seg m ⊂ seg x
    }
    assert set(s.hypotheses) == exp


def test_seg_est_segment_de_seg_non_vacueux():
    s = OBO.seg_est_segment_de_seg("Ro", "o", "m", "x")
    assert s.conclusion not in set(s.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 ordinal_inferieur_ou_egal_sous_iso — la forme LITTÉRALE « seg m ≤ seg x »
#  (au sens des ordinaux), DÉRIVÉE sous la SEULE hypothèse de plus iso_reflexif_seg.
#  → prouve machine-vérifié que le SEUL trou restant est l'ISO IDENTITÉ.
# ─────────────────────────────────────────────────────────────────────────────
def test_ordinal_inf_sous_iso_conclusion():
    t = OBO.ordinal_inferieur_ou_egal_sous_iso("Ro", "o", "m", "x")
    assert t.conclusion == OBO.ordinal_inferieur_ou_egal_litteral("Ro", "o", "m", "x")


def test_ordinal_inf_sous_iso_hypotheses_exactes():
    t = OBO.ordinal_inferieur_ou_egal_sous_iso("Ro", "o", "m", "x")
    Rf = _Rf()
    exp = {
        E.est_bien_ordonne(Rf, var("o")),                              # bon ordre de o
        inclus(seg("Ro", "o", var("m")), seg("Ro", "o", var("x"))),    # seg m ⊂ seg x
        OBO.iso_reflexif_seg("Ro", "o", "m", f="fseg"),                # iso identité (REPORTÉ)
    }
    assert set(t.hypotheses) == exp


def test_ordinal_inf_sous_iso_le_seul_trou_est_iso():
    # la seule hypothèse au-delà de {bon ordre, inclusion} est l'iso identité.
    t = OBO.ordinal_inferieur_ou_egal_sous_iso("Ro", "o", "m", "x")
    Rf = _Rf()
    socle = {
        E.est_bien_ordonne(Rf, var("o")),
        inclus(seg("Ro", "o", var("m")), seg("Ro", "o", var("x"))),
    }
    extra = set(t.hypotheses) - socle
    assert extra == {OBO.iso_reflexif_seg("Ro", "o", "m", f="fseg")}


def test_ordinal_inf_sous_iso_non_vacueux():
    t = OBO.ordinal_inferieur_ou_egal_sous_iso("Ro", "o", "m", "x")
    assert t.conclusion not in set(t.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  iso_reflexif_seg / ordinal_inferieur_ou_egal_litteral — énoncés du REPORT.
# ─────────────────────────────────────────────────────────────────────────────
def test_iso_reflexif_seg_forme():
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
    iso = OBO.iso_reflexif_seg("Ro", "o", "m", f="fseg")
    Rf = _Rf()
    Sm = seg("Ro", "o", var("m"))
    assert iso == V.sont_isomorphes_ordre(Sm, Sm, Rf, Rf, "fseg", "x", "w")


def test_ordinal_inferieur_ou_egal_litteral_forme():
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.ordinaux import ensembles_ordinaux as O
    lit = OBO.ordinal_inferieur_ou_egal_litteral("Ro", "o", "m", "x")
    Rf = _Rf()
    Sm = seg("Ro", "o", var("m"))
    Sx = seg("Ro", "o", var("x"))
    assert lit == O.ordinal_inferieur_ou_egal(Sm, Rf, Sx, Rf, S="Sseg", f="fseg", x="x", y="w")
