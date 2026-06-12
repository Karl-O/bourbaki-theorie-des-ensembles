"""§III.2 — MAILLON FINAL de la trichotomie, contre la CIBLE SAINE (canon).

Le pur ENDGAME LOGIQUE du Théorème 3 §III.2, assemblé contre `trichotomie_ordinaux_canon`
(forme anti-capture, ensembles_iso_ordre_canon) — PAS la forme défaut défectueuse.

    { est_isomorphisme_ordre_canon(h,  D, I, R, Rp),       [h : D ≅ I]
      est_isomorphisme_ordre_canon(hi, I, D, Rp, R),       [hi : I ≅ D (= h⁻¹)]
      ( D = E  ou  I = F ),                                 [maximalité : un segment = le tout]
      est_segment(D, R, E, xo, yo),                         [D segment de E]
      est_segment(I, Rp, F, xo, yo) }                       [I segment de F]
        ⊢  trichotomie_ordinaux_canon(E, R, F, Rp).

Idée : si D=E, alors h : E ≅ I avec I segment de F  ⇒  ordinal_inf_canon(E,R,F,Rp).
       si I=F, alors hi : F ≅ D avec D segment de E  ⇒  ordinal_inf_canon(F,Rp,E,R).
Dans les deux cas la trichotomie (le OU) tient.  Pur assemblage (analyse de cas +
introduction existentielle ×2 + Leibniz) — AUCUNE construction d'iso lourde ici.

RÔLE : montre que l'endgame est assemblé contre la BONNE cible.  L'assemblage complet
instanciera D:=dom h, I:=img h, hi:=reciproque(h), et déchargera les 5 hypothèses depuis
h_est_isomorphisme_ordre (témoins communs), reciproque_isomorphisme_ordre (keystone),
maximalité (adjonction_contredit + prop1) et dom/img segment.  theorie=22, rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, impl, appartient,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, cas,
)
from bourbaki.ordre import ensembles_iso_ordre_canon as C


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_mf"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]  (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ordinal_inf_depuis_iso(e, R, ep, Rp, S_seg, iso_body_proof, h_term):
    """De ⊢ est_isomorphisme_ordre_canon(h, e, S_seg, R, Rp) et est_segment(S_seg, Rp, ep, xo, yo),
    déduit ⊢ ordinal_inferieur_ou_egal_canon(e, R, ep, Rp).

    (∃f)(iso(f,e,S_seg)) par S5 sur f:=h ; conjonction avec est_segment ; (∃S) par S5 sur S:=S_seg."""
    ve, vep = _t(e), _t(ep)
    vS = _t(S_seg)
    # (∃f) est_isomorphisme_ordre_canon(f, e, S_seg, R, Rp)  =  sont_isomorphes_ordre_canon(e,S_seg,R,Rp)
    iso_body = C.est_isomorphisme_ordre_canon(var("f"), ve, vS, R, Rp)
    sont = N.modus_ponens(iso_body_proof, N.s5(iso_body, h_term, "f"))     # (∃f) iso
    # est_segment(S_seg, Rp, ep, xo, yo)
    seg = N.assume(E.est_segment(vS, Rp, vep, C.ISO_X, C.ISO_Y))
    # corps de ordinal_inf à S:=S_seg : et(est_segment(S,Rp,ep), sont_iso(e,S,R,Rp))
    corps_S = conjonction_intro(seg, sont)
    # (∃S) corps  =  ordinal_inferieur_ou_egal_canon(e,R,ep,Rp)
    corps_gen = et(E.est_segment(var("S"), Rp, vep, C.ISO_X, C.ISO_Y),
                   C.sont_isomorphes_ordre_canon(ve, var("S"), R, Rp))
    return N.modus_ponens(corps_S, N.s5(corps_gen, vS, "S"))               # ordinal_inf_canon


def maillon_final(E_set="E", R="R", F_set="F", Rp="Rp", D="D", I="I", h="h", hi="hi"):
    """⊢ { iso_canon(h,D,I,R,Rp), iso_canon(hi,I,D,Rp,R), (D=E ou I=F),
           est_segment(D,R,E,xo,yo), est_segment(I,Rp,F,xo,yo) }
            ⊢ trichotomie_ordinaux_canon(E,R,F,Rp)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vD, vI, vh, vhi = _t(D), _t(I), _t(h), _t(hi)

    # cible = ou(ordinal_inf_canon(E,R,F,Rp), ordinal_inf_canon(F,Rp,E,R))
    gE = C.ordinal_inferieur_ou_egal_canon(vE, Rf, vF, Rpf)
    gF = C.ordinal_inferieur_ou_egal_canon(vF, Rpf, vE, Rf)

    # ── cas D=E : h : E ≅ I, I segment de F  ⇒  ordinal_inf_canon(E,R,F,Rp)
    HDE = N.assume(egal(vD, vE))                                           # D=E
    Hiso = N.assume(C.est_isomorphisme_ordre_canon(vh, vD, vI, Rf, Rpf))   # iso(h,D,I)
    iso_hE = _leib(vD, vE, HDE, lambda w: C.est_isomorphisme_ordre_canon(vh, w, vI, Rf, Rpf), Hiso)
    ord_E = _ordinal_inf_depuis_iso(vE, Rf, vF, Rpf, vI, iso_hE, vh)       # ordinal_inf_canon(E,R,F,Rp)
    tri_caseE = N.modus_ponens(ord_E, N.s2(gE, gF))                        # ou(gE,gF)
    brE = N.loi_deduction(egal(vD, vE), tri_caseE)                         # (D=E) ⇒ tri

    # ── cas I=F : hi : F ≅ D, D segment de E  ⇒  ordinal_inf_canon(F,Rp,E,R)
    HIF = N.assume(egal(vI, vF))                                           # I=F
    Hisoi = N.assume(C.est_isomorphisme_ordre_canon(vhi, vI, vD, Rpf, Rf)) # iso(hi,I,D)
    iso_hiF = _leib(vI, vF, HIF, lambda w: C.est_isomorphisme_ordre_canon(vhi, w, vD, Rpf, Rf), Hisoi)
    ord_F = _ordinal_inf_depuis_iso(vF, Rpf, vE, Rf, vD, iso_hiF, vhi)     # ordinal_inf_canon(F,Rp,E,R)
    tri_caseF0 = N.modus_ponens(ord_F, N.s2(gF, gE))                       # ou(gF,gE)
    tri_caseF = N.modus_ponens(tri_caseF0, N.s3(gF, gE))                   # ou(gE,gF)
    brF = N.loi_deduction(egal(vI, vF), tri_caseF)                         # (I=F) ⇒ tri

    # ── analyse de cas sur la disjonction de maximalité
    Hdisj = N.assume(ou(egal(vD, vE), egal(vI, vF)))
    return cas(Hdisj, brE, brF)                                           # trichotomie_ordinaux_canon(E,R,F,Rp)


def maillon_final_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : trichotomie_ordinaux_canon(E,R,F,Rp)."""
    return C.trichotomie_ordinaux_canon(_t(E_set), _R_de(R), _t(F_set), _R_de(Rp))


def maillon_final_h(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ trichotomie_ordinaux_canon(E,R,F,Rp) avec les 2 hypothèses d'iso DÉCHARGÉES sur
    l'iso maximal h = h_iso_max : on instancie maillon_final à D:=dom h, I:=pr₂ h, h:=h,
    hi:=h⁻¹, et on décharge

      • iso_canon(h, dom h, pr₂ h, R, Rp)   par  h_est_isomorphisme_ordre_sous_hyp
      • iso_canon(h⁻¹, pr₂ h, dom h, Rp, R) par  reciproque_isomorphisme_ordre (keystone)

    Il RESTE en hypothèses (le vrai gap, plus profond) : les 4 conjoints de h_iso
    (func h, compatibilite_inverse_h, compatibilite_ordre_h, surjectivité) + les 2 de
    reciproque (func h, dom h=dom h) + maximalité (dom h=E ou pr₂ h=F) + dom/pr₂ segments.
    Ceci CHAÎNE le maillon final aux pièces commitées — preuve que la cible saine se
    construit depuis l'existant.  theorie=22, rien postulé."""
    import bourbaki.cardinaux.ensembles_trichotomie_scaffold as TS
    import bourbaki.cardinaux.ensembles_trichotomie_h_iso as HI
    import bourbaki.cardinaux.ensembles_iso_ordre_reciproque as RE
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    hi = E.reciproque(h)

    mf = maillon_final(vE, R, vF, Rp, domh, imgh, h, hi)
    # décharge hyp 1 : iso_canon(h, dom h, pr₂ h, R, Rp)
    hyp1 = C.est_isomorphisme_ordre_canon(h, domh, imgh, Rf, Rpf)
    h_iso = HI.h_est_isomorphisme_ordre_sous_hyp(E_set, R, F_set, Rp)
    assert h_iso.conclusion == hyp1, "h_iso ne conclut pas la forme attendue"
    mf = _decharge(mf, hyp1, h_iso)
    # décharge hyp 2 : iso_canon(h⁻¹, pr₂ h, dom h, Rp, R)
    hyp2 = C.est_isomorphisme_ordre_canon(hi, imgh, domh, Rpf, Rf)
    recip = RE.reciproque_isomorphisme_ordre(h, domh, imgh, Rf, Rpf)
    assert recip.conclusion == hyp2, "reciproque ne conclut pas la forme attendue"
    mf = _decharge(mf, hyp2, recip)
    return mf


def _decharge(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


__all__ = ["maillon_final", "maillon_final_cible"]
