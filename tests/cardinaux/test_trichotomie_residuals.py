"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : DÉCHARGE des RÉSIDUS STRUCTURELS.

On certifie (ensembles_trichotomie_residuals) :

  🎯 image_segment_est_segment (CORE) :
        { iso(φ,S,T)[px,pw], func φ, dom φ=S, seg(S0,R,E), seg(T,Rp,F),
          inclus(S0,S), bo(R,E) }  ⊢  est_segment(image(φ,S0), Rp, F).
     « L'image d'un sous-segment par un iso d'ordre est un segment du codomaine. »

  🎯 restriction_inclus_produit_image (CLOS)  : φ|X ⊂ X × image(φ,X).
  🎯 restriction_inclus_produit_Tp            : φ|X resserrée à X × Tp (codomaine partagé).

  🎯🎯 residu_univ_app_renforce (CLOS) : le CONTENU géométrique du résidu (#8 ∧ #13)
        sous ANT_12 RENFORCÉ des 2 segments manquants seg(Sp,R,E)+seg(Tg,Rp,F).

  🎯 dom_h_est_segment_sans_val (CLOS) : seg(dom h) SANS val_dans_F (codomaine DÉRIVÉ
        par le pont clos val_dans_F_depuis_structure).

  🎯🎯 trichotomie_ordinaux_canon_close : trichotomie sous 5 hyps (val_dans_F ÉLIMINÉ).

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Conclusions NON vacueuses.
"""
from bourbaki.logique.formule import var, appartient, egal, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.cardinaux import ensembles_trichotomie_residuals as RES
from bourbaki.cardinaux import ensembles_trichotomie_dom_segment as DS
from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.cardinaux import ensembles_trichotomie_assemble as A
from bourbaki.cardinaux import ensembles_maillon_coherences_prouvees as MCP


def _Rf(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(a, b), vR)


# ════════════════════════════════════════════════════════════════════════════
#  THEORIE INTANGIBLE
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte_22():
    """L'invariant fort : theorie_ensembles() reste = 22 axiomes."""
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CORE — image_segment_est_segment
# ════════════════════════════════════════════════════════════════════════════
def test_image_segment_conclusion():
    """⊢ est_segment(image(φ,S0), Rp, F)  (conclusion == cible)."""
    thm = RES.image_segment_est_segment()
    assert thm.conclusion == RES.image_segment_est_segment_cible()


def test_image_segment_sept_hypotheses_exactes():
    """Exactement 7 hypothèses HONNÊTES : iso, func, dom, 2 segments, inclus(S0,S), bo(R,E)."""
    thm = RES.image_segment_est_segment()
    Rf, Rpf = _Rf("R"), _Rf("Rp")
    attendues = {
        V.est_isomorphisme_ordre(var("phi"), var("S"), var("T"), Rf, Rpf, "px", "pw"),
        E.est_fonctionnel(var("phi")),
        egal(E.dom(var("phi")), var("S")),
        E.est_segment(var("S0"), Rf, var("E")),
        E.est_segment(var("T"), Rpf, var("F")),
        inclus(var("S0"), var("S")),
        E.est_bien_ordonne(Rf, var("E")),
    }
    assert set(thm.hypotheses) == attendues


def test_image_segment_non_vacueux():
    """La conclusion (segment image) n'est AUCUNE des hypothèses."""
    thm = RES.image_segment_est_segment()
    assert thm.conclusion not in set(thm.hypotheses)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 RÉSIDU #13 — restriction incluse dans le produit
# ════════════════════════════════════════════════════════════════════════════
def test_restriction_inclus_produit_image_clos():
    """⊢ φ|X ⊂ X × image(φ,X)  — INCONDITIONNEL (clos)."""
    thm = RES.restriction_inclus_produit_image()
    assert thm.conclusion == RES.restriction_inclus_produit_image_cible()
    assert thm.est_clos


def test_restriction_inclus_produit_Tp_conclusion():
    """⊢ φg|Sp ⊂ Sp × Tp  (resserrage au codomaine partagé Tp)."""
    thm = RES.restriction_inclus_produit_Tp()
    assert thm.conclusion == RES.restriction_inclus_produit_Tp_cible()


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 RÉSIDU RENFORCÉ — le contenu géométrique du résidu, PROUVÉ CLOS
# ════════════════════════════════════════════════════════════════════════════
def test_residu_renforce_clos():
    """⊢ (∀6)((ANT_12 et seg(Sp,R,E) et seg(Tg,Rp,F)) ⇒ (#8 et #13))  CLOS."""
    thm = RES.residu_univ_app_renforce()
    assert thm.conclusion == RES.residu_univ_app_renforce_cible()
    assert thm.est_clos


def test_residu_renforce_meme_consequent_que_depose():
    """Le conséquent (#8 ∧ #13) du renforcé est IDENTIQUE à celui du résidu DÉPOSÉ ;
    seul l'ANTÉCÉDENT diffère (les 2 segments ajoutés)."""
    from bourbaki.cardinaux.ensembles_coincidence_univ_app import _premisse_liste
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    from bourbaki.logique.tactiques.tactiques_abrege2 import _peler_pourtout
    thm = RES.residu_univ_app_renforce()
    f = thm.conclusion
    for _ in range(6):
        _, f = _peler_pourtout(f)
    _, cons = antecedent_consequent(f)
    prem = _premisse_liste("rphip", "rphig", "rSp", "rTp", "rSg", "rTg", "F", "R", "Rp", "E")
    from bourbaki.logique.formule import et
    assert cons == et(prem[8], prem[13])


def test_residu_renforce_antecedent_ajoute_les_2_segments():
    """Les 2 conjoints ajoutés sont seg(Sp,R,E) et seg(Tg,Rp,F)."""
    Rf, Rpf = _Rf("R"), _Rf("Rp")
    seg_Sp = E.est_segment(var("rSp"), Rf, var("E"))
    seg_Tg = E.est_segment(var("rTg"), Rpf, var("F"))
    assert RES.residu_univ_app_renforce_antecedent() == [seg_Sp, seg_Tg]


# ════════════════════════════════════════════════════════════════════════════
#  🎯 R2 — seg(dom h) SANS val_dans_F
# ════════════════════════════════════════════════════════════════════════════
def test_dom_h_segment_sans_val_clos():
    """⊢ est_segment(dom h, R, E)  CLOS (0 hyp) — val_dans_F ÉLIMINÉ."""
    thm = RES.dom_h_est_segment_sans_val()
    assert thm.conclusion == RES.dom_h_est_segment_sans_val_cible()
    assert thm.est_clos


def test_dom_h_segment_sans_val_pas_de_val_dans_F():
    """val_dans_F n'apparaît PAS dans le séquent (codomaine DÉRIVÉ, pas postulé)."""
    thm = RES.dom_h_est_segment_sans_val()
    assert DS.val_dans_F("E", "R", "F", "Rp") not in set(thm.hypotheses)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 ASSEMBLAGE FINAL — trichotomie réduite à 5 hyps (val_dans_F éliminé)
# ════════════════════════════════════════════════════════════════════════════
def test_close_conclusion_est_la_trichotomie():
    """⊢ trichotomie_ordinaux_canon(E,R,F,Rp)  (== maillon_final_cible)."""
    thm = RES.trichotomie_ordinaux_canon_close()
    assert thm.conclusion == RES.trichotomie_ordinaux_canon_close_cible()
    assert thm.conclusion == MCP.maillon_final_h_plus3_cible("E", "R", "F", "Rp")


def test_close_quatre_hypotheses_exactes():
    """Exactement 4 hypothèses : bo(R,E), bo(Rp,F), maximalité, seg(pr₂h,Rp,F)[x,w].
    val_dans_F (présent dans `_min`) est ÉLIMINÉ ; residu_univ_app AUSSI ÉLIMINÉ
    (dérivé de residu_univ_app_renforce, CLOS)."""
    thm = RES.trichotomie_ordinaux_canon_close()
    assert set(thm.hypotheses) == set(RES.trichotomie_ordinaux_canon_close_hypotheses())
    assert len(set(thm.hypotheses)) == 4


def test_close_val_dans_F_elimine():
    """val_dans_F — présent dans trichotomie_ordinaux_canon_prouve_min — est ABSENT."""
    thm = RES.trichotomie_ordinaux_canon_close()
    assert DS.val_dans_F("E", "R", "F", "Rp") not in set(thm.hypotheses)
    # et il EST dans la version _min (régression : on a bien retiré quelque chose)
    mn = A.trichotomie_ordinaux_canon_prouve_min()
    assert DS.val_dans_F("E", "R", "F", "Rp") in set(mn.hypotheses)


def test_close_strictement_moins_d_hypotheses_que_min():
    """trichotomie_ordinaux_canon_close a STRICTEMENT moins d'hypothèses que `_min`."""
    close = RES.trichotomie_ordinaux_canon_close()
    mn = A.trichotomie_ordinaux_canon_prouve_min()
    assert set(close.hypotheses) < set(mn.hypotheses)   # inclusion STRICTE


def test_close_non_vacueux():
    """La conclusion (trichotomie) n'est AUCUNE des 4 hypothèses."""
    thm = RES.trichotomie_ordinaux_canon_close()
    assert thm.conclusion not in set(thm.hypotheses)
