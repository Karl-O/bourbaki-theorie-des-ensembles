"""Tests §III.2 — Théorème 3 (TRICHOTOMIE) : MAXIMALITÉ SUBSTANTIELLE CLOSE
par VARIABLE FRAÎCHE (déblocage de la collision τ).

On certifie (ensembles_maximalite_close) :

  🎯🎯 maximalite_donne_trichotomie_close :
        { bo(R,E), bo(Rp,F),
          est_segment(dom h,R,E), est_segment(pr₂h,Rp,F), inclus(h,dom h×pr₂h) }
          ⊢ ( dom h = E ) ou ( pr₂ h = F )   ( == maximalite_donne_trichotomie ).
        ⚠️ `residu_univ_app` ÉLIMINÉ (dérivé de residu_univ_app_renforce, CLOS).

Le point CENTRAL : le RÉSIDU (3) (iso de h⁺ pour R/Rp), τ-BLOQUÉ dans
maximalite_donne_trichotomie_prouve (le pont iso_hplus_pour_R_majorants_discharges
NE SE CONSTRUIT PAS au témoin τ), est ICI DÉRIVÉ — car les variables a,b sont
introduites FRAÎCHES (existe_elimination), donc ATOMIQUES, sans collision de binders.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Conclusion NON vacueuse.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient, libres_f
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.maximalite import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.coincidence_fusion import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.maximalite import ensembles_maximalite_adjoint_bridge as ADJB
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.maximalite import ensembles_maximalite_close as MC


def _R_de(R):
    vR = var(R)
    return lambda a, b: appartient(E.couple(var(a) if isinstance(a, str) else a,
                                            var(b) if isinstance(b, str) else b), vR)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 LE FIX — la VARIABLE FRAÎCHE résolvait la collision τ ; depuis le fix subst
#     (2026-07-24), le pont se CONSTRUIT AUSSI directement au témoin τ.
# ════════════════════════════════════════════════════════════════════════════
def test_pont_construit_a_variable_fraiche():
    """iso_hplus_pour_R_majorants_discharges SE CONSTRUIT à la variable fraîche « a »."""
    thm = ADJB.iso_hplus_pour_R_majorants_discharges("E", "R", "F", "Rp", "a", "b")
    assert thm.conclusion == ADJB.iso_hplus_pour_R_cible("E", "R", "F", "Rp", "a", "b")


def test_pont_construit_aussi_au_temoin_tau():
    """Depuis le fix subst, le pont SE CONSTRUIT au témoin τx(…) : l'ancienne
    « collision » (binder interne du τ vs binders fixes du recollement) était un
    renommage GRATUIT de la substitution, supprimé par le court-circuit CS."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import tau, et, egal, pourtout, impl
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import seg as _seg
    h = TS.h_iso_max("E", "R", "F", "Rp")
    domh, imgh = E.dom(h), E.img(h)

    def _tau(R_, e_, d_):
        ve, vd = var(e_), d_
        DmD = E.difference(ve, vd)
        Rg = _R_de(R_)
        petit = et(appartient(var("x"), DmD),
                   pourtout("w", impl(appartient(var("w"), DmD), Rg(var("x"), var("w")))))
        return tau("x", et(petit, egal(vd, _seg(R_, e_, var("x")))))

    a_star, b_star = _tau("R", "E", domh), _tau("Rp", "F", imgh)
    thm = ADJB.iso_hplus_pour_R_majorants_discharges("E", "R", "F", "Rp", a_star, b_star)
    assert thm.conclusion == ADJB.iso_hplus_pour_R_cible("E", "R", "F", "Rp", a_star, b_star)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 LE THÉORÈME — maximalite_donne_trichotomie_close.
# ════════════════════════════════════════════════════════════════════════════
def test_close_conclusion():
    thm = MC.maximalite_donne_trichotomie_close()
    # conclusion == maximalite_donne_trichotomie(...) == ( dom h=E ou pr₂h=F )
    assert thm.conclusion == MC.maximalite_donne_trichotomie_close_cible()
    assert thm.conclusion == M.maximalite_donne_trichotomie("E", "R", "F", "Rp")
    assert thm.conclusion.tag == "ou"
    assert thm.conclusion not in thm.hypotheses                  # NON vacueux


def test_close_hypotheses():
    thm = MC.maximalite_donne_trichotomie_close()
    assert not thm.est_clos
    hyps = set(thm.hypotheses)
    # EXACTEMENT 5 : 2 HONNÊTES + 2 segments + h_graphe_hyp  (residu_univ_app ÉLIMINÉ)
    expected = set(MC.maximalite_donne_trichotomie_close_hypotheses())
    assert len(expected) == 5
    assert hyps == expected
    # 2 HONNÊTES présentes
    honnetes = set(FDA.fusion_depuis_coincidence_app_hypotheses("E", "R", "F", "Rp"))
    assert len(honnetes) == 2
    assert honnetes <= hyps
    # les 2 segments + h-graphe
    h = TS.h_iso_max("E", "R", "F", "Rp")
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    assert E.est_segment(E.dom(h), Rf, var("E")) in hyps
    assert E.est_segment(E.img(h), Rpf, var("F")) in hyps
    assert MC.h_graphe_hyp("E", "R", "F", "Rp") in hyps


def test_close_hypotheses_toutes_ab_independantes():
    """Les 5 hypothèses survivantes sont TOUTES a,b-INDÉPENDANTES (elles survivent
    à existe_elimination — c'est ce qui rend la clôture possible)."""
    thm = MC.maximalite_donne_trichotomie_close()
    for hh in thm.hypotheses:
        free = libres_f(hh)
        assert "a" not in free, f"a libre dans {hh!r}"
        assert "b" not in free, f"b libre dans {hh!r}"


def test_close_residu3_resolu():
    """Le RÉSIDU (3) — iso de h⁺ pour R/Rp — N'EST PLUS une hypothèse (DÉRIVÉ via
    le pont à variable fraîche)."""
    thm = MC.maximalite_donne_trichotomie_close()
    # aucune hypothèse n'est un est_isomorphisme_ordre de h⁺ (le résidu (3) τ-bloqué)
    for hh in thm.hypotheses:
        # un iso est encodé et(bijective, compatible) = ¬(¬∨¬) ; ce n'est pas notre cas
        assert hh != ADJB.iso_hplus_pour_R_cible("E", "R", "F", "Rp", "a", "b")


# ════════════════════════════════════════════════════════════════════════════
#  INVARIANT global : theorie_ensembles() intacte = 22.
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_intacte():
    MC.maximalite_donne_trichotomie_close()
    assert len(E.theorie_ensembles().axiomes) == 22
