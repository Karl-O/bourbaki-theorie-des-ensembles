"""§III.2 — COMPARABILITÉ de deux segments ABSTRAITS d'un bon ordre (brique de Lemme 1).

    { est_bien_ordonne(R,E),  est_segment(S,R,E),  est_segment(S',R,E) }
        ⊢  ( S ⊂ S' )  ou  ( S' ⊂ S ).

Deux segments initiaux d'un bon ordre sont toujours EMBOÎTÉS.  Première brique de
`fusion_hyp` (Lemme 1 §III.2).

PREUVE par cas (S=E / propre) × (S'=E / propre) :
  • S=E : S'⊂E=S ⇒ S'⊂S.       • S'=E : S⊂E=S' ⇒ S⊂S'.
  • S,S' propres : Prop 1 (CLOS) ⇒ S=seg(a), S'=seg(b), a,b∈E ; comparabilite_segments_
    temoins (CLOS) ⇒ seg(a)⊂seg(b) ou seg(b)⊂seg(a) ; Leibniz ⇒ S⊂S' ou S'⊂S.
theorie=22, non vacueux.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, egal, ou, non, appartient, inclus, tau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_elim_gauche, conjonction_elim_droite, instancie, equivalence_avant,
    cas, tiers_exclu,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.temoins_comparabilite import ensembles_trichotomie_prop1 as P1
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences.ensembles_trichotomie_restriction import (
    comparabilite_segments_temoins,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import seg


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_sca"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _decharge(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _sym(a, b, h_ab):
    """⊢ a=b  ⟹  ⊢ b=a."""
    return N.modus_ponens(h_ab, symetrie(_t(a), _t(b)))


def _or_g(preuve_A, A, B):
    """⊢ A  ⟹  ⊢ (A ou B)."""
    return N.modus_ponens(preuve_A, N.s2(A, B))


def _or_d(preuve_B, A, B):
    """⊢ B  ⟹  ⊢ (A ou B)   (via s2(B,A) puis s3 : (B ou A)⇒(A ou B))."""
    return N.modus_ponens(N.modus_ponens(preuve_B, N.s2(B, A)), N.s3(B, A))


def _prop1_seg_form(R, E_set, S_name):
    """{bo, est_segment(S,R,E), S≠E} ⊢ (a, ⊢S=seg(R,E,a), ⊢a∈E)  (Prop 1 + existe_temoin)."""
    vE = _t(E_set)
    thm = P1.prop1_segment_propre(R, E_set, S_name)
    body = thm.conclusion.sous[0]                       # corps de ∃x
    a = tau("x", body)
    wit = N.modus_ponens(thm, N.existe_temoin(body, "x"))
    S_eq_seg = conjonction_elim_droite(wit)             # S = seg(R,E,a)
    pp = conjonction_elim_gauche(wit)                   # est_plus_petit_element(R,E∖S,a)
    a_in_diff = conjonction_elim_gauche(pp)             # a ∈ E∖S
    ax_diff = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    diff_eq = instancie(instancie(instancie(ax_diff, vE), _t(S_name)), a)  # a∈E∖S ⇔ (a∈E et a∉S)
    a_in_E = conjonction_elim_gauche(
        N.modus_ponens(a_in_diff, equivalence_avant(diff_eq)))
    return a, S_eq_seg, a_in_E


# @livre Ch.III §2.1 Prop.2 | E III.16 L.21-30 | PDF p.119  (E* bien ordonné par inclusion ⇒ deux segments quelconques sont emboîtés)
def segments_abstraits_comparables(R="R", E_set="E", S="S", Sp="Sp"):
    """⊢ { est_bien_ordonne(R,E), est_segment(S,R,E), est_segment(S',R,E) }
            ⊢ ( S ⊂ S' ) ou ( S' ⊂ S )."""
    Rf = _R_de(R)
    vE, vS, vSp = _t(E_set), _t(S), _t(Sp)
    A, B = inclus(vS, vSp), inclus(vSp, vS)             # goal = ou(A,B)
    HsegS = N.assume(E.est_segment(vS, Rf, vE))
    HsegSp = N.assume(E.est_segment(vSp, Rf, vE))
    S_inc_E = conjonction_elim_gauche(HsegS)            # S⊂E
    Sp_inc_E = conjonction_elim_gauche(HsegSp)          # S'⊂E

    # ── cas S=E :  S'⊂E=S ⇒ S'⊂S = B ──
    HSeqE = N.assume(egal(vS, vE))
    SpS = _leib(vE, vS, _sym(vS, vE, HSeqE), lambda w: inclus(vSp, w), Sp_inc_E)  # S'⊂S
    br_SeqE = N.loi_deduction(egal(vS, vE), _or_d(SpS, A, B))

    # ── cas S≠E ──
    a, S_eq_sega, a_in_E = _prop1_seg_form(R, E_set, S)
    sega = seg(R, E_set, a)
    #   sous-cas S'=E : S⊂E=S' ⇒ S⊂S' = A
    HSpeqE = N.assume(egal(vSp, vE))
    SSp = _leib(vE, vSp, _sym(vSp, vE, HSpeqE), lambda w: inclus(vS, w), S_inc_E)  # S⊂S'
    br_SpeqE = N.loi_deduction(egal(vSp, vE), _or_g(SSp, A, B))
    #   sous-cas S'≠E : comparabilité seg(a),seg(b)
    b, Sp_eq_segb, b_in_E = _prop1_seg_form(R, E_set, Sp)
    segb = seg(R, E_set, b)
    comp = comparabilite_segments_temoins(R, E_set, a, b)
    comp = _decharge(comp, appartient(a, vE), a_in_E)
    comp = _decharge(comp, appartient(b, vE), b_in_E)
    #     branche seg(a)⊂seg(b) ⇒ S⊂S' = A
    Hl = N.assume(inclus(sega, segb))
    l1 = _leib(sega, vS, _sym(vS, sega, S_eq_sega), lambda w: inclus(w, segb), Hl)   # S⊂seg(b)
    l2 = _leib(segb, vSp, _sym(vSp, segb, Sp_eq_segb), lambda w: inclus(vS, w), l1)  # S⊂S'
    brl = N.loi_deduction(inclus(sega, segb), _or_g(l2, A, B))
    #     branche seg(b)⊂seg(a) ⇒ S'⊂S = B
    Hr = N.assume(inclus(segb, sega))
    r1 = _leib(segb, vSp, _sym(vSp, segb, Sp_eq_segb), lambda w: inclus(w, sega), Hr)  # S'⊂seg(a)
    r2 = _leib(sega, vS, _sym(vS, sega, S_eq_sega), lambda w: inclus(vSp, w), r1)      # S'⊂S
    brr = N.loi_deduction(inclus(segb, sega), _or_d(r2, A, B))
    goal_pp = cas(comp, brl, brr)                      # ou(A,B)  [.., S≠E, S'≠E]

    # recombine S'=E / S'≠E
    teSp = tiers_exclu(egal(vSp, vE))
    goal_Sne = cas(teSp, br_SpeqE, N.loi_deduction(non(egal(vSp, vE)), goal_pp))
    # recombine S=E / S≠E
    teS = tiers_exclu(egal(vS, vE))
    return cas(teS, br_SeqE, N.loi_deduction(non(egal(vS, vE)), goal_Sne))


def segments_abstraits_comparables_cible(R="R", E_set="E", S="S", Sp="Sp"):
    vS, vSp = _t(S), _t(Sp)
    return ou(inclus(vS, vSp), inclus(vSp, vS))


__all__ = ["segments_abstraits_comparables", "segments_abstraits_comparables_cible"]
