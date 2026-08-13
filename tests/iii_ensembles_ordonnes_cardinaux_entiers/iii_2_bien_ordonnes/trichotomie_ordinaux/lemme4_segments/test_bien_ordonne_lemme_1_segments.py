"""Tests MIROIR — ensembles_bien_ordonne_lemme_1_segments : OSSATURE de
l'ISOMORPHISME D'ORDRE  t ↦ seg_ext(a,R,t)  d'un ensemble bien ordonné (a,R) sur
ses segments propres ordonnés par ⊂  (lemme L1a, brique de L1).

INVARIANT vérifié partout : theorie_ensembles() = 22.
Anti-tautologie : aucune conclusion n'est l'une de ses hypothèses.  Hypothèses
EXACTES contrôlées.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient, inclus, egal, et, non, ou, impl, pourtout,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_lemme_1_segments as L1


def _Rf():
    return lambda x, y: appartient(E.couple(x, y), var("R"))


# ─────────────────────────────────────────────────────────────────────────────
#  theorie_ensembles INTANGIBLE = 22
# ─────────────────────────────────────────────────────────────────────────────
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 seg_strict_monotone_de_bon_ordre — sens DIRECT de l'iso, déchargé sur le
#  SEUL bon ordre de (a,R) : { est_bien_ordonne(R,a), R{t,s} } ⊢ seg(t)⊂seg(s).
# ─────────────────────────────────────────────────────────────────────────────
def test_mono_de_bon_ordre_conclusion():
    m = L1.seg_strict_monotone_de_bon_ordre("R", "a", "t", "s")
    St = L1.seg("R", "a", "t")
    Ss = L1.seg("R", "a", "s")
    assert m.conclusion == inclus(St, Ss)


def test_mono_de_bon_ordre_hypotheses_exactes():
    m = L1.seg_strict_monotone_de_bon_ordre("R", "a", "t", "s")
    Rf = _Rf()
    exp = {
        Rf(var("t"), var("s")),                 # R{t,s}
        E.est_bien_ordonne(Rf, var("a")),       # bon ordre de (a,R)
    }
    assert set(m.hypotheses) == exp


def test_mono_de_bon_ordre_non_vacueux():
    m = L1.seg_strict_monotone_de_bon_ordre("R", "a", "t", "s")
    assert m.conclusion not in set(m.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  🎯 segment_extremite_est_segment — INITIALITÉ : chaque seg(a,R,t) est un VRAI
#  SEGMENT de (a,R) (Définition 2), sous le SEUL bon ordre.  INCONDITIONNEL.
# ─────────────────────────────────────────────────────────────────────────────
def test_est_segment_conclusion():
    g = L1.segment_extremite_est_segment("R", "a", "t")
    assert g.conclusion == L1.segment_extremite_est_segment_cible("R", "a", "t")


def test_est_segment_conclusion_litterale():
    # la conclusion est LITTÉRALEMENT est_segment(seg(a,R,t), R, a) (binders x,y canoniques)
    g = L1.segment_extremite_est_segment("R", "a", "t")
    Rf = _Rf()
    seg = L1.seg("R", "a", "t")
    assert g.conclusion == E.est_segment(seg, Rf, var("a"))


def test_est_segment_hypothese_unique():
    g = L1.segment_extremite_est_segment("R", "a", "t")
    Rf = _Rf()
    assert set(g.hypotheses) == {E.est_bien_ordonne(Rf, var("a"))}


def test_est_segment_non_vacueux():
    g = L1.segment_extremite_est_segment("R", "a", "t")
    # la conclusion est_segment(…) n'est PAS l'hypothèse bon ordre
    assert g.conclusion not in set(g.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  ⚠️ seg_reflechit_ordre — sens RÉCIPROQUE de l'iso (order-reflecting),
#  conditionné à la COMPARABILITÉ (totalité) et s∈a :
#  { (R{t,s} ou R{s,t}), s∈a } ⊢ (seg(t)⊂seg(s)) ⇒ R{t,s}.
# ─────────────────────────────────────────────────────────────────────────────
def test_reflechit_conclusion():
    r = L1.seg_reflechit_ordre("R", "a", "t", "s")
    assert r.conclusion == L1.seg_reflechit_ordre_cible("R", "a", "t", "s")


def test_reflechit_conclusion_litterale():
    r = L1.seg_reflechit_ordre("R", "a", "t", "s")
    Rf = _Rf()
    St = L1.seg("R", "a", "t")
    Ss = L1.seg("R", "a", "s")
    assert r.conclusion == impl(inclus(St, Ss), Rf(var("t"), var("s")))


def test_reflechit_hypotheses_exactes():
    r = L1.seg_reflechit_ordre("R", "a", "t", "s")
    Rf = _Rf()
    exp = {
        ou(Rf(var("t"), var("s")), Rf(var("s"), var("t"))),   # comparabilité de t,s
        appartient(var("s"), var("a")),                       # s ∈ a
    }
    assert set(r.hypotheses) == exp


def test_reflechit_non_vacueux():
    r = L1.seg_reflechit_ordre("R", "a", "t", "s")
    # la conclusion (seg(t)⊂seg(s))⇒R{t,s} n'est aucune hypothèse
    assert r.conclusion not in set(r.hypotheses)
    assert len(E.theorie_ensembles().axiomes) == 22


# ─────────────────────────────────────────────────────────────────────────────
#  comparables_dans — forme littérale de l'hypothèse de comparabilité.
# ─────────────────────────────────────────────────────────────────────────────
def test_comparables_dans_forme():
    c = L1.comparables_dans("R", "a", "t", "s")
    Rf = _Rf()
    assert c == ou(Rf(var("t"), var("s")), Rf(var("s"), var("t")))


# ─────────────────────────────────────────────────────────────────────────────
#  COHÉRENCE iso : sur le bon ordre + comparabilité + s∈a, on a les DEUX sens
#  (seg(t)⊂seg(s) ⇒ R{t,s})  et  (R{t,s} ⇒ seg(t)⊂seg(s)) — l'ossature d'iso.
#  (vérification structurelle : conclusions miroir compatibles.)
# ─────────────────────────────────────────────────────────────────────────────
def test_iso_deux_sens_compatibles():
    Rf = _Rf()
    St = L1.seg("R", "a", "t")
    Ss = L1.seg("R", "a", "s")
    direct = L1.seg_strict_monotone_de_bon_ordre("R", "a", "t", "s")    # R{t,s} ⊢ seg(t)⊂seg(s)
    reciproque = L1.seg_reflechit_ordre("R", "a", "t", "s")             # ⊢ seg(t)⊂seg(s) ⇒ R{t,s}
    # sens direct : conclusion seg(t)⊂seg(s) ; R{t,s} est en hypothèse
    assert direct.conclusion == inclus(St, Ss)
    assert Rf(var("t"), var("s")) in set(direct.hypotheses)
    # sens réciproque : conclusion (seg(t)⊂seg(s)) ⇒ R{t,s}
    assert reciproque.conclusion == impl(inclus(St, Ss), Rf(var("t"), var("s")))
