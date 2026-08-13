"""Tests MIROIR — ensembles_segments_ordinaux : RÉDUCTION de hyp_bon_ordre_seg au
BON ORDRE DES INDICES (voie Zermelo), pour l'arc cardinaux_bien_ordonnes → ℕ.

INVARIANT vérifié : theorie_ensembles() = 22 ; conclusion == hyp_bon_ordre_seg
LITTÉRALEMENT ; hypothèses EXACTES = bon ordre des indices + S≠∅ + seg_monotone ;
NON vacueux ; existence Zermelo CLOSE.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, non, egal, appartient, libres_f,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_segments_ordinaux as SO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.bon_ordre_intervalle.ensembles_clause_plus_petit_correspondance import (
    hyp_bon_ordre_seg, hyp_surjection,
)


def _T_default(S="S", a="a", R="R"):
    """L'ordre des indices opaque par défaut de SO (lambda u,v)."""
    Tset = E.app("ord_indices", var(a), var(R), var(S))
    return lambda u, v: appartient(E.couple(u, v), Tset)


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 LA RÉDUCTION — conclusion == hyp_bon_ordre_seg LITTÉRALEMENT, 3 hyps exactes.
# ─────────────────────────────────────────────────────────────────────────────
def test_hyp_bon_ordre_seg_de_bon_ordre_indices_conclusion():
    t = SO.hyp_bon_ordre_seg_de_bon_ordre_indices("a", "R", "S")
    # conclusion == la pièce (2) LITTÉRALEMENT (binders ms,xs)
    assert t.conclusion == hyp_bon_ordre_seg("a", "R", "S", "ms", "xs")


def test_hyp_bon_ordre_seg_de_bon_ordre_indices_hypotheses_exactes():
    t = SO.hyp_bon_ordre_seg_de_bon_ordre_indices("a", "R", "S")
    hyps = set(t.hypotheses)
    vS = var("S")
    T = _T_default()
    exp_ne = non(egal(vS, E.VIDE))                                  # S ≠ ∅
    exp_mono = SO.seg_monotone("a", "R", "S", T)                    # monotonie
    exp_bo = E.est_bien_ordonne(T, vS, "xo", "yo", "zo", "S", "ms", "xs")  # bon ordre indices
    assert hyps == {exp_ne, exp_mono, exp_bo}


def test_hyp_bon_ordre_seg_non_vacueux():
    t = SO.hyp_bon_ordre_seg_de_bon_ordre_indices("a", "R", "S")
    # NON vacueux : la conclusion n'est aucune des hypothèses
    assert t.conclusion not in set(t.hypotheses)


# ─────────────────────────────────────────────────────────────────────────────
#  seg_monotone — forme de l'isomorphisme d'ordre (report).
# ─────────────────────────────────────────────────────────────────────────────
def test_seg_monotone_forme():
    T = _T_default()
    f = SO.seg_monotone("a", "R", "S", T)
    # report_seg_monotone == seg_monotone avec le T par défaut
    assert SO.report_seg_monotone("a", "R", "S") == f
    # quantifie bien sur deux indices (∀us)(∀vs) — ∀ = ¬∃¬, le binder externe est « us »
    assert f.tag == "non" and f.sous[0].lieur == "us"


# ─────────────────────────────────────────────────────────────────────────────
#  report_surjection == hyp_surjection (l'autre pièce, énoncée).
# ─────────────────────────────────────────────────────────────────────────────
def test_report_surjection_forme():
    assert SO.report_surjection("a", "R", "S") == hyp_surjection("a", "R", "S", "xs")


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 EXISTENCE d'un bon ordre des indices (Zermelo) — CLOS, 0 hyp, theorie=22.
# ─────────────────────────────────────────────────────────────────────────────
def test_bon_ordre_indices_existe_clos():
    z = SO.bon_ordre_indices_existe("S")
    assert z.est_clos
    assert not z.hypotheses
    # (∃R) est_bien_ordonne(R_R, S)  — seule variable libre = S, tête ∃R
    assert sorted(libres_f(z.conclusion)) == ["S"]
    assert z.conclusion.lieur == "R"
    assert len(E.theorie_ensembles().axiomes) == 22
