"""§III.2 — CONSTRUCTION COUVRANTE (cœur de l'assemblage de fusion_hyp, Lemme 1).

Étant donné, pour deux couples (u,v),(u',v') de h, les segments-témoins EMBOÎTÉS S₁⊂S₂
(comparabilité, brique 1) et la COÏNCIDENCE des isos sur le chevauchement (φ₁=φ₂ sur S₁),
le PLUS GRAND iso (φ₂:S₂≅T₂) couvre les DEUX antécédents :

    { est_segment(S₂,R,E), est_segment(T₂,Rp,F), iso(φ₂,S₂,T₂),   [témoin du 2ᵉ, le grand]
      u∈S₁,  S₁⊂S₂,  v=φ₁(u),  φ₁(u)=φ₂(u),                       [1ᵉʳ point + coïncidence]
      u'∈S₂,  v'=φ₂(u') }                                          [2ᵉ point, dans le grand]
        ⊢  temoin_commun_h(u,v,u',v').

(u∈S₂ par S₁⊂S₂ ; v=φ₂(u) par v=φ₁(u) et φ₁(u)=φ₂(u) ; puis ∃-intro (S₂,T₂,φ₂).)

C'est la moitié « S₁⊂S₂ » de l'assemblage ; la moitié symétrique S₂⊂S₁ est analogue.
Réduit fusion_hyp à : extraction des 2 témoins + comparabilité (brique 1, FAITE) +
COÏNCIDENCE.  theorie=22, non vacueux.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, appartient, inclus, existe
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro, instancie
from bourbaki.cardinaux.ensembles_trichotomie_coherences import _temoin_commun_coeur


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_tcv"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    va, vb = _t(a), _t(b)
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# binders d'iso canoniques du scaffold/temoin
_ISO_X, _ISO_Y = "px", "pw"


def temoin_commun_couvrant(E_set="E", R="R", F_set="F", Rp="Rp",
                           u="u", v="v", up="up", vp="vp",
                           S1="S1", S2="S2", T2="T2", phi1="phi1", phi2="phi2"):
    """⊢ { seg S₂, seg T₂, iso(φ₂,S₂,T₂), u∈S₁, S₁⊂S₂, v=φ₁(u), φ₁(u)=φ₂(u),
           u'∈S₂, v'=φ₂(u') } ⊢ temoin_commun_h(u,v,u',v')  (via (S₂,T₂,φ₂))."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vu, vv, vup, vvp = _t(u), _t(v), _t(up), _t(vp)
    vS1, vS2, vT2 = _t(S1), _t(S2), _t(T2)
    vphi1, vphi2 = _t(phi1), _t(phi2)
    phi2_u = E.valeur(vphi2, vu)                         # φ₂(u)
    phi1_u = E.valeur(vphi1, vu)                         # φ₁(u)

    # ── hypothèses ──
    Hseg_S2 = N.assume(E.est_segment(vS2, Rf, vE))
    Hseg_T2 = N.assume(E.est_segment(vT2, Rpf, vF))
    Hiso2 = N.assume(V.est_isomorphisme_ordre(vphi2, vS2, vT2, Rf, Rpf, _ISO_X, _ISO_Y))
    Hu_S1 = N.assume(appartient(vu, vS1))               # u∈S₁
    HS1_S2 = N.assume(inclus(vS1, vS2))                 # S₁⊂S₂
    Hv_eq = N.assume(egal(vv, phi1_u))                  # v=φ₁(u)
    Hcoinc = N.assume(egal(phi1_u, phi2_u))             # φ₁(u)=φ₂(u)
    Hup_S2 = N.assume(appartient(vup, vS2))             # u'∈S₂
    Hvp_eq = N.assume(egal(vvp, E.valeur(vphi2, vup)))  # v'=φ₂(u')

    # ── u∈S₂  (S₁⊂S₂ instancié à u) ──
    Hu_S2 = N.modus_ponens(Hu_S1, instancie(HS1_S2, vu))   # u∈S₂

    # ── v=φ₂(u)  (v=φ₁(u) et φ₁(u)=φ₂(u)) ──
    Hv_eq2 = _leib(phi1_u, phi2_u, Hcoinc, lambda w: egal(vv, w), Hv_eq)   # v=φ₂(u)

    # cœur à coordonnées-TERMES (≡ _temoin_commun_coeur mais accepte des termes pour S,T,φ)
    def _coeur(sS, sT, sphi):
        return et(et(et(et(et(et(
            E.est_segment(sS, Rf, vE),
            E.est_segment(sT, Rpf, vF)),
            V.est_isomorphisme_ordre(sphi, sS, sT, Rf, Rpf, _ISO_X, _ISO_Y)),
            appartient(vu, sS)),
            appartient(vup, sS)),
            egal(vv, E.valeur(sphi, vu))),
            egal(vvp, E.valeur(sphi, vup)))

    # ── cœur(S₂,T₂,φ₂) prouvé ──
    coeur_proof = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(conjonction_intro(conjonction_intro(
            Hseg_S2, Hseg_T2), Hiso2), Hu_S2), Hup_S2), Hv_eq2), Hvp_eq)
    assert coeur_proof.conclusion == _coeur(vS2, vT2, vphi2), "coeur mismatch"

    # ── ∃-intro (binders « phi », « T », « S » de temoin_commun_h ; témoins φ₂,T₂,S₂) ──
    bphi = _coeur(vS2, vT2, var("phi"))
    ex_phi = N.modus_ponens(coeur_proof, N.s5(bphi, vphi2, "phi"))   # (∃φ)…
    bT = existe("phi", _coeur(vS2, var("T"), var("phi")))
    ex_T = N.modus_ponens(ex_phi, N.s5(bT, vT2, "T"))                # (∃T)(∃φ)…
    bS = existe("T", existe("phi", _coeur(var("S"), var("T"), var("phi"))))
    ex_S = N.modus_ponens(ex_T, N.s5(bS, vS2, "S"))                  # (∃S)(∃T)(∃φ)… = temoin_commun_h
    return ex_S


def temoin_commun_couvrant_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                 u="u", v="v", up="up", vp="vp"):
    """ÉNONCÉ-cible : temoin_commun_h(u,v,u',v')."""
    from bourbaki.cardinaux.ensembles_trichotomie_coherences import temoin_commun_h
    return temoin_commun_h(E_set, R, F_set, Rp, u, v, up, vp)


__all__ = ["temoin_commun_couvrant", "temoin_commun_couvrant_cible"]
