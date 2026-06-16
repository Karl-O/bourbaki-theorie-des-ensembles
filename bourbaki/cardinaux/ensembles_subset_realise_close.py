"""§III.2/§III.4 — vers `subset_realise_segment` : « tout B⊂a est équipotent à un
segment initial de (a,Ro) » via la TRICHOTOMIE (Th3 §III.2) appliquée à (B,ordre
induit) vs (a,Ro), en RÉCUPÉRANT func/dom du témoin `h` (et NON du ∃f abstrait).

────────────────────────────────────────────────────────────────────────────────
LA ROUTE (correction 2 de la mission — h-derivé, PAS le ∃f nu).

La machinerie de la trichotomie (Th3 §III.2) est CLOSE aux 2 SEULES honnêtes
{bo(R,E),bo(Rp,F)} pour des noms AMBIANTS canoniques E,R,F,Rp.  Toutes les briques
h-niveau (h_est_iso_prouve, fonctionnel_h_prouve, maximalite via est_un_graphe +
h_est_graphe, dom_h_est_segment_sans_val, pr2_h_est_segment) se RÉDUISENT à {bo,bo}.

🔑 LE DÉBLOCAGE.  Bien que ces lemmes ASSERTENT les noms canoniques au moment de
LEUR construction, une fois leurs hypothèses DÉCHARGÉES en implication
`(bo(R,E) et bo(Rp,F)) ⇒ Conclusion(h_iso_max(E,R,F,Rp))`, le résultat est CLOS
(0 hyp) ⇒ on peut GÉNÉRALISER (∀E)(∀R)(∀F)(∀Rp) puis INSTANCIER à des TERMES
CONCRETS.  On pose alors  E:=B,  R:=graphe_induit(Ro,B),  F:=a,  Rp:=Ro  et le
témoin devient  h' := h_iso_max(B, graphe_induit(Ro,B), a, Ro)  — un TERME CONCRET
(SANS la variable « F » ⇒ aucun piège de capture dans bijection_implique_equipotent).
`bo(graphe_induit(Ro,B), B)` est lui-même PROUVÉ par `bo_induit_B` sous {bo(Ro,a),
B⊆a} (ensembles_ordre_induit_sousensemble).

DE LÀ, sous { bo(_R_de(Ro),a),  B⊆a } :
  • iso_h'   : est_isomorphisme_ordre(h', dom h', pr₂h', Rind, Ro)   [h_est_iso] ;
  • func_h'  : est_fonctionnel(h')                                   [fonctionnel_h] ;
  • max_h'   : ( dom h' = B )  ou  ( pr₂h' = a )                     [maximalité] ;
  • seg_dom' : est_segment(dom h', Rind, B)                          [dom_seg, CLOS] ;
  • seg_pr2' : est_segment(pr₂h', Ro, a)                             [pr2_seg, CLOS].

BRANCHE `dom h' = B` :  réécriture dom h'→B dans iso_h' (Leibniz), puis
`iso_implique_equipotent(h', B, pr₂h', Rind, Ro, x, w)` (CLOS) RECOMPOSE
est_bijection_de(h',B,pr₂h') via func_h' + (dom h'=B) ⇒ **Eq(B, pr₂h')**.  Et pr₂h'
est un SEGMENT de (a,Ro) ; s'il est PROPRE (≠a), `prop1_segment_propre_clos` donne
pr₂h'=seg(a,Ro,t) pour t=min(a∖pr₂h')∈a ⇒ Eq(B, seg(a,Ro,t)).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (theorie_ensembles=22 ; rien postulé du but) — voir RAPPORT
pour le statut EXACT de la clôture finale et l'arête B=a.

INVARIANT : theorie_ensembles() = 22.  Hypothèses HONNÊTES : { bo(_R_de(Ro),a),
B⊆a } (+ le cas de branche).  NON vacueux.  NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant,
)

from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_maximalite_substantielle as MS
from bourbaki.cardinaux import ensembles_maillon_coherences_prouvees as MCP
from bourbaki.cardinaux import ensembles_trichotomie_hgraphe_pr2seg as HGP
from bourbaki.cardinaux import ensembles_trichotomie_residuals as RES
from bourbaki.cardinaux import ensembles_h_est_graphe as HG
from bourbaki.cardinaux import ensembles_ordre_induit_sousensemble as OI
from bourbaki.cardinaux import ensembles_realisation_segment_close as RSC
from bourbaki.cardinaux.ensembles_segments_construction import _R_de, seg
from bourbaki.cardinaux.ensembles_cardinaux import equipotent


def _t(t):
    return t if isinstance(t, Terme) else var(t)


_HOLE = "hole_srcl"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]  (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  discharge → generalize(E,R,F,Rp) → instantiate aux TERMES CONCRETS.
# ════════════════════════════════════════════════════════════════════════════
def _dgi_decharge(thm, ordre_hyps, concrete, preuves):
    """Décharge les hyps de `thm` dans l'ORDRE `ordre_hyps` (loi_deduction successives,
    le DERNIER déchargé devient l'antécédent EXTERNE), généralise (∀E)(∀R)(∀F)(∀Rp),
    instancie aux 4 termes `concrete`, puis DÉCHARGE les antécédents par modus_ponens
    avec `preuves` (appariées dans l'ordre INVERSE de la décharge = ordre des antécédents).

    `ordre_hyps`/`preuves` doivent matcher : preuves[i] prouve l'instance de ordre_hyps[i].
    PRÉCONDITION : thm.hypotheses == set(ordre_hyps) (sur E,R,F,Rp), thm devient clos."""
    assert set(thm.hypotheses) == set(ordre_hyps), "ordre_hyps ≠ hyps de thm"
    out = thm
    for h in ordre_hyps:                       # décharge : H0 d'abord (antécédent INTERNE),
        out = N.loi_deduction(h, out)          # Hk en dernier (antécédent EXTERNE)
    assert out.est_clos, "thm non clos après décharge"
    # généralisation E,R,F,Rp : Rp devient le ∀ EXTERNE ⇒ instancier en ordre INVERSE.
    for nm in ["E", "R", "F", "Rp"]:
        out = N.generalisation(nm, out)
    for c in reversed(concrete):               # [Rp,F,R,E] = concrete inversé
        out = instancie(out, c)
    # antécédents en ordre EXTERNE→INTERNE = ordre_hyps inversé ; preuves dans le même ordre
    for p in reversed(preuves):
        out = N.modus_ponens(p, out)
    return out


# ════════════════════════════════════════════════════════════════════════════
#  Briques h-niveau INSTANCIÉES à (B, graphe_induit(Ro,B), a, Ro).
# ════════════════════════════════════════════════════════════════════════════
def h_prime(Ro="Ro", a="asr", B="Bsr"):
    """Le témoin maximal INSTANCIÉ :  h' := h_iso_max(B, graphe_induit(Ro,B), a, Ro).

    TERME CONCRET — ne contient PAS la variable « F », donc bijection_implique_
    equipotent (s5 sur le binder « F ») ne capture rien."""
    return TS.h_iso_max(_t(B), OI.graphe_induit(Ro, B), _t(a), _t(Ro))


def _concrete(Ro, a, B):
    """Le 4-uplet d'instanciation (E,R,F,Rp) := (B, graphe_induit(Ro,B), a, Ro)."""
    return [_t(B), OI.graphe_induit(Ro, B), _t(a), _t(Ro)]


def _hyp_porte(hyp, nom_graphe):
    """Teste si l'hypothèse bo `hyp` (forme est_bien_ordonne(_R_de(nom),·)) porte le
    graphe `nom_graphe` (R ou Rp).  Repère par appartenance de var(nom_graphe) aux
    variables libres de hyp."""
    from bourbaki.logique.formule import libres_f
    return nom_graphe in libres_f(hyp)


def _via_h(thm_canon, Ro, a, B):
    """Décharge thm_canon (hyps = {bo(R,E), bo(Rp,F)} aux binders RÉELS du théorème)
    → gén(E,R,F,Rp) → inst(B,Rind,a,Ro) → re-décharge par les bo concrets.

    Les 2 hyps sont APPARIÉES par le graphe qu'elles portent : celle sur R devient
    bo(Rind,B) (prouvée par bo_induit_B), celle sur Rp devient bo(Ro,a) (assumée).
    On lit les hyps RÉELLES de thm_canon (binders inconnus a priori) pour éviter tout
    mismatch de liant."""
    hyps = list(thm_canon.hypotheses)
    assert len(hyps) == 2, f"attendu 2 bo, obtenu {len(hyps)}"
    # apparier : hyp_R porte « R » (et pas « Rp »), hyp_Rp porte « Rp »
    hyp_R = next(h for h in hyps if _hyp_porte(h, "R") and not _hyp_porte(h, "Rp"))
    hyp_Rp = next(h for h in hyps if _hyp_porte(h, "Rp"))
    bo_Rind_B = OI.bo_induit_B(Ro, a, B)                       # [bo(Ro,a), B⊆a]  prouve bo(Rind,B)
    bo_Ro_a = N.assume(E.est_bien_ordonne(_R_de(Ro), _t(a)))   # bo(Ro,a) honnête
    # ordre_hyps = [hyp_R, hyp_Rp]  ⟷  preuves = [bo_Rind_B, bo_Ro_a]
    return _dgi_decharge(thm_canon, [hyp_R, hyp_Rp],
                         _concrete(Ro, a, B), [bo_Rind_B, bo_Ro_a])


def iso_h_prime(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a), B⊆a } ⊢ est_isomorphisme_ordre(h', dom h', pr₂h', Rind, Ro, x, w).

    h_est_iso_prouve DÉCHARGÉ→GÉNÉRALISÉ→INSTANCIÉ à (B,graphe_induit(Ro,B),a,Ro),
    puis les 2 bo's concrets fournis (bo_induit_B + bo(Ro,a))."""
    return _via_h(MS.h_est_iso_prouve(), Ro, a, B)


def func_h_prime(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a), B⊆a } ⊢ est_fonctionnel(h').  (fonctionnel_h_prouve via _via_h.)"""
    return _via_h(MCP.fonctionnel_h_prouve(), Ro, a, B)


def maximalite_h_prime(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a), B⊆a } ⊢ ( dom h' = B )  ou  ( pr₂h' = a ).

    maximalite_close_via_est_un_graphe (sous {bo,bo,est_un_graphe(h)}) avec
    est_un_graphe(h) DÉCHARGÉ par h_est_graphe (CLOS) AVANT la généralisation (il
    porte E,R,F,Rp via h), puis _via_h."""
    mx = HGP.maximalite_close_via_est_un_graphe()              # [bo, bo, est_un_graphe(h)]
    h = TS.h_iso_max("E", "R", "F", "Rp")
    graphe_hyp = E.est_un_graphe(h)
    assert graphe_hyp in set(mx.hypotheses), "est_un_graphe(h) absent des hyps de maximalité"
    hg = HG.h_est_graphe()                                     # CLOS
    assert hg.conclusion == graphe_hyp
    mx = N.modus_ponens(hg, N.loi_deduction(graphe_hyp, mx))   # [bo, bo]
    return _via_h(mx, Ro, a, B)


def seg_dom_h_prime(Ro="Ro", a="asr", B="Bsr"):
    """⊢ est_segment(dom h', Rind, B)   (CLOS — dom_h_est_segment_sans_val instancié)."""
    ds = RES.dom_h_est_segment_sans_val()                      # CLOS
    return _gen_inst_clos(ds, Ro, a, B)


def seg_pr2_h_prime(Ro="Ro", a="asr", B="Bsr"):
    """⊢ est_segment(pr₂h', Ro, a)   (CLOS — pr2_h_est_segment instancié)."""
    ps = HGP.pr2_h_est_segment()                               # CLOS
    return _gen_inst_clos(ps, Ro, a, B)


def _gen_inst_clos(thm_clos, Ro, a, B):
    """Généralise (∀E)(∀R)(∀F)(∀Rp) un théorème CLOS et l'instancie à (B,Rind,a,Ro)
    (instanciation en ordre INVERSE de la généralisation)."""
    assert thm_clos.est_clos, "thm non clos"
    out = thm_clos
    for nm in ["E", "R", "F", "Rp"]:
        out = N.generalisation(nm, out)
    for c in reversed(_concrete(Ro, a, B)):
        out = instancie(out, c)
    return out


# ════════════════════════════════════════════════════════════════════════════
#  BRANCHE dom h' = B  →  Eq(B, pr₂h').  (RÉCUPÉRATION func/dom du témoin h'.)
# ════════════════════════════════════════════════════════════════════════════
def eq_B_pr2_sous_dom_eq_B(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a), B⊆a, dom h' = B } ⊢ Eq( B , pr₂h' ).

    🎯 LE CŒUR — l'iso d'ordre h' de B sur pr₂h' AUGMENTÉ de func/dom DONNE l'équipotence.
    Sous dom h'=B : on réécrit le 1ᵉʳ argument de iso_h' (dom h' → B, Leibniz), puis
    `iso_implique_equipotent(h', B, pr₂h', Rind, Ro, x, w)` (CLOS) recompose
    est_bijection_de(h',B,pr₂h') via func_h' + (dom h'=B).  pr₂h' n'est PAS réécrit
    (il reste img(h')).  theorie=22."""
    vh = h_prime(Ro, a, B)
    domh, imgh = E.dom(vh), E.img(vh)
    vB = _t(B)
    Rind_f = OI.Rind(Ro, B)
    Rof = _R_de(Ro)

    iso = iso_h_prime(Ro, a, B)                 # est_iso(h', dom h', pr₂h', Rind, Ro, x, w)
    func = func_h_prime(Ro, a, B)               # est_fonctionnel(h')
    H_dom = N.assume(egal(domh, vB))            # dom h' = B

    # réécrire dom h' → B dans la formule iso (Leibniz)
    iso_B = _leib(domh, vB, H_dom,
                  lambda w: V.est_isomorphisme_ordre(vh, w, imgh, Rind_f, Rof, x="x", y="w"),
                  iso)                          # est_iso(h', B, pr₂h', Rind, Ro)
    # iso_implique_equipotent(h', B, pr₂h', Rind, Ro, x, w) : (iso ∧ func ∧ dom=B) ⇒ Eq(B,pr₂h')
    iie = RSC.iso_implique_equipotent(f=vh, X=vB, Y=imgh, R=OI.graphe_induit(Ro, B),
                                      Rp=_t(Ro), x="x", y="w")
    triple = conjonction_intro(conjonction_intro(iso_B, func), H_dom)
    eq = N.modus_ponens(triple, iie)            # Eq(B, pr₂h')
    assert eq.conclusion == equipotent(vB, imgh), "conclusion ≠ Eq(B, pr₂h')"
    return eq


def eq_B_pr2_sous_dom_eq_B_cible(Ro="Ro", a="asr", B="Bsr"):
    """ÉNONCÉ-cible (test miroir) : Eq( B , pr₂h' )."""
    vh = h_prime(Ro, a, B)
    return equipotent(_t(B), E.img(vh))


__all__ = [
    "h_prime", "iso_h_prime", "func_h_prime", "maximalite_h_prime",
    "seg_dom_h_prime", "seg_pr2_h_prime",
    "eq_B_pr2_sous_dom_eq_B", "eq_B_pr2_sous_dom_eq_B_cible",
]
