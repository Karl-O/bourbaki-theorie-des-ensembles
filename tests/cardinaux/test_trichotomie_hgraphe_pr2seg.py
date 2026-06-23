"""Tests — §III.2 Th3 TRICHOTOMIE : décharge pr₂h-segment (TARGET 2), h-graphe
(TARGET 1) et assemblage close-v2.

VÉRIFIE (theorie=22, rien postulé, NON vacueux) :
  • TARGET 2 `pr2_h_est_segment` : est_segment(pr₂h,Rp,F) CLOS (0 hyp).
  • TARGET 1 `h_inclus_dom_pr2` : inclus(h,dom h×pr₂h) (== h_graphe_hyp) sous l'unique
    hypothèse est_un_graphe(h) (résidu opaque irréductible, strictement plus faible).
  • `maximalite_close_via_est_un_graphe` : (dom h=E ∨ pr₂h=F) sous {bo,bo,
    est_un_graphe(h)}  (residu_univ_app ÉLIMINÉ).
  • `trichotomie_ordinaux_canon_close_v2` : trichotomie_ordinaux_canon SOUS
    {bo(R,E), bo(Rp,F), est_un_graphe(h)} (== maillon_final_cible).
"""
from bourbaki.cardinaux import ensembles_trichotomie_hgraphe_pr2seg as HG
from bourbaki.cardinaux import ensembles_maximalite_close as MAX
from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.formule import appartient, var


def _Rf(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


# ── TARGET 2 ─────────────────────────────────────────────────────────────────
def test_pr2_h_est_segment_clos():
    th = HG.pr2_h_est_segment()
    assert th.est_clos, "pr2_h_est_segment doit être CLOS (0 hyp)"
    assert len(list(th.hypotheses)) == 0


def test_pr2_h_est_segment_conclusion():
    th = HG.pr2_h_est_segment()
    assert th.conclusion == HG.pr2_h_est_segment_cible()


def test_pr2_h_est_segment_theorie_22():
    HG.pr2_h_est_segment()
    assert len(E.theorie_ensembles().axiomes) == 22


# ── TARGET 1 ─────────────────────────────────────────────────────────────────
def test_h_inclus_dom_pr2_conclusion_egale_h_graphe_hyp():
    th = HG.h_inclus_dom_pr2()
    assert th.conclusion == HG.h_inclus_dom_pr2_cible()
    assert th.conclusion == MAX.h_graphe_hyp()


def test_h_inclus_dom_pr2_unique_hyp_est_un_graphe():
    th = HG.h_inclus_dom_pr2()
    h = TS.h_iso_max()
    assert list(th.hypotheses) == [E.est_un_graphe(h)], \
        "l'unique hypothèse doit être est_un_graphe(h) (résidu opaque)"


def test_h_inclus_dom_pr2_non_vacueux():
    th = HG.h_inclus_dom_pr2()
    assert th.conclusion not in set(th.hypotheses)


# ── maximalité via est_un_graphe ─────────────────────────────────────────────
def test_maximalite_close_via_est_un_graphe():
    mc = HG.maximalite_close_via_est_un_graphe()
    assert mc.conclusion == HG.maximalite_close_via_est_un_graphe_cible()
    h = TS.h_iso_max()
    bo_R = E.est_bien_ordonne(_Rf("R"), var("E"))
    bo_Rp = E.est_bien_ordonne(_Rf("Rp"), var("F"))
    honn = set(FDA.fusion_depuis_coincidence_app_hypotheses())
    expected = honn | {E.est_un_graphe(h)}
    assert set(mc.hypotheses) == expected, \
        "maximalité doit survivre sous {bo,bo,est_un_graphe(h)}  (residu_univ_app ÉLIMINÉ)"


# ── assemblage close-v2 ──────────────────────────────────────────────────────
def test_close_v2_conclusion_est_trichotomie():
    v2 = HG.trichotomie_ordinaux_canon_close_v2()
    assert v2.conclusion == HG.trichotomie_ordinaux_canon_close_v2_cible()


def test_close_v2_hypotheses_sont_bo_bo_est_un_graphe():
    v2 = HG.trichotomie_ordinaux_canon_close_v2()
    attendu = set(HG.trichotomie_ordinaux_canon_close_v2_hypotheses())
    assert set(v2.hypotheses) == attendu
    assert len(list(v2.hypotheses)) == 3   # {bo, bo, est_un_graphe} — residu_univ_app ÉLIMINÉ
    # contenu précis
    h = TS.h_iso_max()
    bo_R = E.est_bien_ordonne(_Rf("R"), var("E"))
    bo_Rp = E.est_bien_ordonne(_Rf("Rp"), var("F"))
    hs = set(v2.hypotheses)
    assert bo_R in hs and bo_Rp in hs
    assert E.est_un_graphe(h) in hs


def test_close_v2_non_vacueux():
    v2 = HG.trichotomie_ordinaux_canon_close_v2()
    assert v2.conclusion not in set(v2.hypotheses)


def test_close_v2_theorie_22():
    HG.trichotomie_ordinaux_canon_close_v2()
    assert len(E.theorie_ensembles().axiomes) == 22
