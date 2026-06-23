"""Tests — §III.2 Th3 TRICHOTOMIE : `est_un_graphe(h)` PROUVÉ (forme SET de h) et
décharge de close-v3 → hyps {bo, bo} = Théorème 3 §III.2 CLOS.

VÉRIFIE (theorie_ensembles=22, rien postulé du but, NON vacueux) :
  • Forme SET `h_membre_set` : z∈h ⇔ (∃a)(∃b)(z=(a,b) et corps_h(a,b)), instanciée.
  • FIDÉLITÉ `h_membre_depuis_set` : la forme SET ENTAÎNE la forme COUPLE déposée
    (== TS.h_membre(cu,cv)), CLOS.
  • FIDÉLITÉ FORTE `axiome_h_depuis_set` : la forme SET ENTAÎNE l'AXIOME COUPLE déposé
    (== TS.axiome_h(…,cu,cv), α-représentant canonique), CLOS.
  • `h_est_graphe` : est_un_graphe(h) CLOS (0 hyp).
  • `trichotomie_ordinaux_canon_close_v3` : trichotomie_ordinaux_canon SOUS
    {bo(R,E), bo(Rp,F)} (est_un_graphe(h) ET residu_univ_app DÉCHARGÉS) = Théorème 3 CLOS.
"""
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.h_coherences import ensembles_h_est_graphe as HGr
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.h_coherences import ensembles_trichotomie_hgraphe_pr2seg as HG
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.coincidence_fusion import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import appartient, var


def _Rf(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


# ── Forme SET : instance d'axiome (theorie dédiée) ────────────────────────────
def test_h_membre_set_clos():
    th = HGr.h_membre_set()
    assert th.est_clos and len(list(th.hypotheses)) == 0


def test_theorie_ensembles_intangible_set():
    HGr.h_membre_set()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_h_graphe_un_seul_axiome():
    th = HGr.theorie_h_graphe()
    assert len(th.axiomes) == 1
    # le nouvel axiome N'EST PAS dans theorie_ensembles
    assert th.axiomes[0] not in set(E.theorie_ensembles().axiomes)


# ── FIDÉLITÉ : set-form ENTAÎNE la couple-form déposée ────────────────────────
def test_h_membre_depuis_set_clos():
    th = HGr.h_membre_depuis_set()
    assert th.est_clos, "doit être CLOS (0 hyp) — dérivé sous theorie_h_graphe"
    assert len(list(th.hypotheses)) == 0


def test_h_membre_depuis_set_egale_h_membre_depose():
    """La forme SET ENTAÎNE EXACTEMENT TS.h_membre (couple-form déposée), aux
    coordonnées fraîches cu,cv (sans clash de liant interne)."""
    th = HGr.h_membre_depuis_set()
    assert th.conclusion == HGr.h_membre_depuis_set_cible()
    assert th.conclusion == TS.h_membre("E", "R", "F", "Rp", "cu", "cv").conclusion


def test_h_membre_depuis_set_non_vacueux():
    th = HGr.h_membre_depuis_set()
    assert th.conclusion not in set(th.hypotheses)


# ── FIDÉLITÉ FORTE : set-form ENTAÎNE l'AXIOME couple déposé verbatim ──────────
def test_axiome_h_depuis_set_clos():
    th = HGr.axiome_h_depuis_set()
    assert th.est_clos and len(list(th.hypotheses)) == 0


def test_axiome_h_depuis_set_egale_axiome_h_depose():
    """🎯🎯 La forme SET (axiome_h_graphe) ENTAÎNE l'AXIOME COUPLE déposé TS.axiome_h
    (binders frais cu,cv = α-représentant canonique) : RENFORCEMENT CONSERVATIF."""
    th = HGr.axiome_h_depuis_set()
    assert th.conclusion == HGr.axiome_h_depuis_set_cible()
    assert th.conclusion == TS.axiome_h("E", "R", "F", "Rp", "cu", "cv")


# ── est_un_graphe(h) PROUVÉ depuis la forme SET ───────────────────────────────
def test_h_est_graphe_clos():
    th = HGr.h_est_graphe()
    assert th.est_clos, "est_un_graphe(h) doit être CLOS (0 hyp)"
    assert len(list(th.hypotheses)) == 0


def test_h_est_graphe_conclusion():
    th = HGr.h_est_graphe()
    assert th.conclusion == HGr.h_est_graphe_cible()
    h = TS.h_iso_max()
    assert th.conclusion == E.est_un_graphe(h)


def test_h_est_graphe_non_vacueux():
    th = HGr.h_est_graphe()
    assert th.conclusion not in set(th.hypotheses)


def test_h_est_graphe_theorie_22():
    HGr.h_est_graphe()
    assert len(E.theorie_ensembles().axiomes) == 22


# ── close-v3 : est_un_graphe(h) DÉCHARGÉ → {bo, bo} = Théorème 3 §III.2 CLOS ─────
def test_close_v3_conclusion_est_trichotomie():
    v3 = HGr.trichotomie_ordinaux_canon_close_v3()
    assert v3.conclusion == HGr.trichotomie_ordinaux_canon_close_v3_cible()
    # == conclusion de close-v2 (== trichotomie_ordinaux_canon == maillon_final_cible)
    assert v3.conclusion == HG.trichotomie_ordinaux_canon_close_v2_cible()


def test_close_v3_hypotheses_sont_bo_bo():
    """🎯🎯 THÉORÈME 3 §III.2 CLOS : v3 a EXACTEMENT {bo(R,E), bo(Rp,F)} = la prémisse
    propre du théorème.  residu_univ_app ET est_un_graphe(h) ÉLIMINÉS."""
    v3 = HGr.trichotomie_ordinaux_canon_close_v3()
    attendu = set(HGr.trichotomie_ordinaux_canon_close_v3_hypotheses())
    assert set(v3.hypotheses) == attendu
    assert len(list(v3.hypotheses)) == 2
    # bo(R,E), bo(Rp,F) présents — ET SEULS
    bo_R = E.est_bien_ordonne(_Rf("R"), var("E"))
    bo_Rp = E.est_bien_ordonne(_Rf("Rp"), var("F"))
    hs = set(v3.hypotheses)
    assert bo_R in hs and bo_Rp in hs
    assert hs == {bo_R, bo_Rp}


def test_close_v3_residu_univ_app_elimine():
    """🎯🎯 residu_univ_app N'EST PLUS une hypothèse de v3 (dérivé de
    residu_univ_app_renforce, CLOS) — la dernière pièce géométrique est PAYÉE."""
    v3 = HGr.trichotomie_ordinaux_canon_close_v3()
    assert FDA.residu_univ_app("E", "R", "F", "Rp") not in set(v3.hypotheses)


def test_close_v3_est_un_graphe_discharged():
    """est_un_graphe(h) NE figure PLUS parmi les hypothèses (déchargé par h_est_graphe)."""
    v3 = HGr.trichotomie_ordinaux_canon_close_v3()
    h = TS.h_iso_max()
    assert E.est_un_graphe(h) not in set(v3.hypotheses)


def test_close_v3_egale_v2_moins_est_un_graphe():
    """close-v3 = close-v2 avec est_un_graphe(h) déchargé (même conclusion)."""
    v3 = HGr.trichotomie_ordinaux_canon_close_v3()
    v2 = HG.trichotomie_ordinaux_canon_close_v2()
    h = TS.h_iso_max()
    assert v3.conclusion == v2.conclusion
    assert set(v3.hypotheses) == set(v2.hypotheses) - {E.est_un_graphe(h)}


def test_close_v3_honnetes_sont_fusion_hyps():
    """Les 2 hyps survivantes == les hyps HONNÊTES de la fusion (bo,bo)."""
    v3 = HGr.trichotomie_ordinaux_canon_close_v3()
    honn = set(FDA.fusion_depuis_coincidence_app_hypotheses())
    assert set(v3.hypotheses) == honn


def test_close_v3_non_vacueux():
    v3 = HGr.trichotomie_ordinaux_canon_close_v3()
    assert v3.conclusion not in set(v3.hypotheses)


def test_close_v3_theorie_22():
    HGr.trichotomie_ordinaux_canon_close_v3()
    assert len(E.theorie_ensembles().axiomes) == 22
