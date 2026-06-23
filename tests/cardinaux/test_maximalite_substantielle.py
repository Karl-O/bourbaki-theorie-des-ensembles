"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : MAXIMALITÉ SUBSTANTIELLE de h.

On certifie (ensembles_maximalite_substantielle) :

  🎯🎯 TARGET A — h_est_iso_prouve :
        { bo(R,E), bo(Rp,F) } ⊢ est_isomorphisme_ordre(h,dom h,pr₂ h,R,Rp).
     Les 2 SEULES hypothèses survivantes = celles des cohérences prouvées (HONNÊTES).
     ⚠️ `residu_univ_app` ÉLIMINÉ (dérivé de residu_univ_app_renforce, CLOS).

  🎯🎯 TARGET B — maximalite_donne_trichotomie_prouve :
        { bo(R,E), bo(Rp,F), 2 segments, 4 RÉSIDU back-and-forth }
          ⊢ ( dom h = E ) ou ( pr₂ h = F )   ( == maximalite_donne_trichotomie ).
     RÉSIDU précisément reporté (le pont ≤'⇔R sur le segment fermé) ; JAMAIS postulé.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Conclusions NON vacueuses.
"""
from bourbaki.logique.formule import var, egal, ou, non, appartient, Formule
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_h_iso as HI
from bourbaki.cardinaux import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.cardinaux import ensembles_maximalite_substantielle as MS


def _R_de(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(var(a) if isinstance(a, str) else a,
                                            var(b) if isinstance(b, str) else b), vR)


# ════════════════════════════════════════════════════════════════════════════
#  ✅ image_dom_egale_img : image(G, dom G) = pr₂(G).  INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def test_image_dom_egale_img_clos():
    thm = MS.image_dom_egale_img("G")
    assert thm.est_clos and not thm.hypotheses
    assert thm.conclusion == MS.image_dom_egale_img_cible("G")
    # = est_surjective(G, dom G, pr₂ G)
    assert thm.conclusion == E.est_surjective(var("G"), E.dom(var("G")), E.img(var("G")))


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 TARGET A — h_est_iso_prouve : h iso d'ordre de dom h sur pr₂ h.
# ════════════════════════════════════════════════════════════════════════════
def test_h_est_iso_prouve_conclusion():
    thm = MS.h_est_iso_prouve()
    # conclusion == est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp)
    assert thm.conclusion == MS.h_est_iso_prouve_cible()
    assert thm.conclusion == HI.h_est_isomorphisme_ordre_sous_hyp_cible()
    assert thm.conclusion not in thm.hypotheses              # NON vacueux


def test_h_est_iso_prouve_hypotheses_honnetes():
    thm = MS.h_est_iso_prouve()
    assert not thm.est_clos
    # EXACTEMENT les 2 hypothèses HONNÊTES {bo(R,E), bo(Rp,F)} — residu_univ_app ÉLIMINÉ
    expected = set(MS.h_est_iso_prouve_hypotheses())
    assert len(expected) == 2
    assert set(thm.hypotheses) == expected
    # = celles de la fusion (coïncidence CLOSE)
    assert set(thm.hypotheses) == set(
        FDA.fusion_depuis_coincidence_app_hypotheses("E", "R", "F", "Rp"))


def test_h_est_iso_prouve_aucune_cohérence_residuelle():
    """Les 4 hypothèses de h_est_isomorphisme_ordre_sous_hyp sont TOUTES déchargées."""
    thm = MS.h_est_iso_prouve()
    h = TS.h_iso_max("E", "R", "F", "Rp")
    domh, imgh = E.dom(h), E.img(h)
    # aucune des 4 hypothèses-cohérences ne survit
    assert E.est_fonctionnel(h) not in thm.hypotheses
    assert HI.compatibilite_inverse_h() not in thm.hypotheses
    assert HI.compatibilite_ordre_h() not in thm.hypotheses
    assert E.est_surjective(h, domh, imgh) not in thm.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  TARGET B — pièce : (a,b)∈h sous résidu structurel.
# ════════════════════════════════════════════════════════════════════════════
def test_couple_ab_dans_h_residu():
    thm = MS.couple_ab_dans_h_residu()
    assert not thm.est_clos
    assert thm.conclusion == MS.couple_ab_dans_h_residu_cible()
    assert thm.conclusion not in thm.hypotheses              # NON vacueux
    # les 4 résidus structurels sont présents
    residu = MS.couple_ab_dans_h_residu_hyps()
    assert len(residu) == 4
    for r in residu:
        assert r in thm.hypotheses
    # 9 hyps : 4 résidu + dom h=seg(R,E,a) + a∈E + b∈F + func h + a∉dom h
    assert len(thm.hypotheses) == 9


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 TARGET B — maximalite_donne_trichotomie_prouve : dom h=E ou pr₂h=F.
# ════════════════════════════════════════════════════════════════════════════
def test_maximalite_donne_trichotomie_conclusion():
    thm = MS.maximalite_donne_trichotomie_prouve()
    # conclusion == maximalite_donne_trichotomie(...) == (dom h=E ou pr₂h=F)
    assert thm.conclusion == MS.maximalite_donne_trichotomie_prouve_cible()
    assert thm.conclusion == M.maximalite_donne_trichotomie("E", "R", "F", "Rp")
    assert thm.conclusion.tag == "ou"
    assert thm.conclusion not in thm.hypotheses              # NON vacueux


def test_maximalite_donne_trichotomie_hypotheses():
    thm = MS.maximalite_donne_trichotomie_prouve()
    assert not thm.est_clos
    hyps = set(thm.hypotheses)
    # 2 HONNÊTES {bo(R,E), bo(Rp,F)} — residu_univ_app ÉLIMINÉ
    honnetes = set(FDA.fusion_depuis_coincidence_app_hypotheses("E", "R", "F", "Rp"))
    assert honnetes <= hyps
    # 4 RÉSIDU back-and-forth (au témoin a*,b*)
    residu = set(MS.maximalite_donne_trichotomie_prouve_residu())
    assert len(residu) == 4
    assert residu <= hyps
    # 2 SEGMENTS (dom h, pr₂ h)
    h = TS.h_iso_max("E", "R", "F", "Rp")
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    seg_dom = E.est_segment(E.dom(h), Rf, var("E"))
    seg_img = E.est_segment(E.img(h), Rpf, var("F"))
    assert seg_dom in hyps and seg_img in hyps
    # AUCUNE autre hypothèse : 2 + 4 + 2 = 8, parfaitement classées
    classified = honnetes | residu | {seg_dom, seg_img}
    assert hyps == classified
    assert len(hyps) == 8


def test_maximalite_residu_est_le_gap_precis():
    """Le RÉSIDU 3 = l'iso de h⁺* w.r.t. R/Rp (et non les ordres adjoints) — le GAP."""
    residu = MS.maximalite_donne_trichotomie_prouve_residu()
    assert len(residu) == 4
    # le 3ᵉ résidu EST l'iso (R,Rp) de h⁺* sur les segments fermés ]←,a*]≅]←,b*]
    h = TS.h_iso_max("E", "R", "F", "Rp")
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    from bourbaki.cardinaux import ensembles_trichotomie_temoin_adjonction as ADJ
    from bourbaki.logique.formule import tau, et as _et, pourtout, impl
    # τ-témoins (reconstruits comme dans la preuve)
    domh, imgh = E.dom(h), E.img(h)
    from bourbaki.cardinaux.ensembles_segments_construction import seg as _seg
    def _tau(R_, e_, d_):
        ve, vd = var(e_), d_
        DmD = E.difference(ve, vd)
        Rg = _R_de(R_)
        petit_x = _et(appartient(var("x"), DmD),
                      pourtout("w", impl(appartient(var("w"), DmD), Rg(var("x"), var("w")))))
        body_x = _et(petit_x, egal(vd, _seg(R_, e_, var("x"))))
        return tau("x", body_x)
    a_star, b_star = _tau("R", "E", domh), _tau("Rp", "F", imgh)
    hplus = ADJ.temoin_adjonction("E", "R", "F", "Rp", a_star, b_star)
    SaA = V.ensemble_adjoint(_seg("R", "E", a_star), a_star)
    TbB = V.ensemble_adjoint(_seg("Rp", "F", b_star), b_star)
    iso_attendu = V.est_isomorphisme_ordre(hplus, SaA, TbB, Rf, Rpf, "px", "pw")
    assert residu[2] == iso_attendu
    # et c'est bien un est_isomorphisme_ordre (= et(bijective, compatible), encodé ¬(¬∨¬))
    assert iso_attendu.tag == "non"


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    # construire les deux targets ne touche pas la théorie
    MS.h_est_iso_prouve()
    MS.maximalite_donne_trichotomie_prouve()
    assert len(E.theorie_ensembles().axiomes) == 22
