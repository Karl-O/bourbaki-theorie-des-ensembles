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
CE QUE CE MODULE LIVRE (theorie_ensembles=22 ; rien postulé du but) :

  ✅ les 5 briques h-niveau INSTANCIÉES à (B,graphe_induit(Ro,B),a,Ro), réduites aux
     SEULES honnêtes { bo(Ro,a), B⊆a } (iso/func/maximalité) ou CLOSES (les 2 segments) ;
  🎯 `eq_B_pr2_sous_dom_eq_B`  : { bo, B⊆a, dom h'=B } ⊢ Eq(B, pr₂h')  (func/dom récupérés) ;
  🎯 `pr2_eq_seg_exists`       : { bo, pr₂h'≠a } ⊢ ∃t(t∈a et pr₂h'=seg(Ro,a,t)) (Prop 1) ;
  🎯 `realise_segment_pour_B_sans_dom` :
        { bo(Ro,a),  B⊆a,  ¬(pr₂h'=a) }  ⊢  (∃t)( t∈a et Eq( B , seg(Ro,a,t) ) ).
     soit la conclusion de subset_realise_segment POUR CE B sous l'UNIQUE condition de
     branche HONNÊTE `¬(pr₂h'=a)` (= « B n'épuise pas a » ; pr₂h'=a ssi B est order-iso
     à TOUT a, donc équipotent à a).
  🎯 `equipotent_implique_inf_egal` (CLOS) : Eq(X,Y) ⇒ X≤Y (bijection = injection) ;
  🎯 `pr2_eq_a_donne_eq_B_a` : { bo, B⊆a, pr₂h'=a } ⊢ Eq(B,a)  (via Eq(dom h',a),
     dom h'⊆B, B⊆a, CANTOR-BERNSTEIN) — donc ¬Eq(B,a) ⇒ ¬(pr₂h'=a) (contraposée) ;
  🎯🎯 `realise_segment_pour_B_clean` — LA FORME PROPRE/INTERPRÉTABLE :
        { bo(Ro,a),  B⊆a,  ¬Eq(B,a) }  ⊢  (∃t)( t∈a et Eq( B , seg(Ro,a,t) ) ).
     La condition de branche est la CARDINALE HONNÊTE `¬Eq(B,a)` (« B strictement plus
     court que a »), qui EST la condition VRAIE : tout B⊆a NON équipotent à a est
     équipotent à un segment PROPRE seg(Ro,a,t).  C'est le THÉORÈME DE REPRÉSENTATION
     ORDINALE (effondrement de Mostowski) RESTREINT — et CLOS — au cas honnête B≁a.

⚠️⚠️ STATUT du `subset_realise_segment` LITTÉRAL (∀B, INCLUANT B=a) — il N'EST PAS
clos, et ne PEUT pas l'être : pour B=a la conclusion exige Eq(a, seg(Ro,a,t)) avec
seg PROPRE (strict, E.III.2.1), FAUX pour a fini (segment propre = a privé d'un élément)
ET pour le cardinal TOP Card(a).  Le maillon `realisation_garde_depuis_subset`
(ensembles_realisation_segment_close) instancie `subset_realise_segment` en B=image(F,c)
pour TOUT cardinal c≤a, DONC en c=Card(a) (le top) ⇒ exige Eq(B,a) avec un segment
PROPRE : structurellement impossible.  Le `¬(pr₂h'=a)` survivant EST exactement cette
obstruction : pour B « plus court » que a il s'élimine (B order-iso à un segment propre),
pour B=a il TIENT (B épuise a).  Voir RAPPORT pour la sortie possible (réénoncer le GATE
sur c<Card(a), restructurant pullback_onto).

INVARIANT : theorie_ensembles() = 22.  Hypothèses HONNÊTES : { bo(_R_de(Ro),a),
B⊆a, ¬(pr₂h'=a) }.  NON vacueux.  NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, appartient, existe, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, cas,
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


# ════════════════════════════════════════════════════════════════════════════
#  pr₂h' est un SEGMENT PROPRE ⇒ pr₂h' = seg(Ro,a,t) pour t = min(a∖pr₂h') ∈ a.
# ════════════════════════════════════════════════════════════════════════════
def pr2_eq_seg_exists(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a),  pr₂h' ≠ a }  ⊢  (∃t)( t∈a  et  pr₂h' = seg(Ro,a,t) ).

    🎯 pr₂h' est un SEGMENT de (a,Ro) (seg_pr2_h_prime, CLOS) ; PROPRE (≠a, hyp branche).
    `prop1_segment_propre_clos(Ro,a,pr₂h')` (E.III.2.1) donne alors un x = min(a∖pr₂h')
    avec pr₂h'=seg(Ro,a,x) ; x∈a∖pr₂h' ⇒ x∈a (AXIOME_DIFF).  On bâtit (∃t)(t∈a et
    pr₂h'=seg(Ro,a,t)).  theorie=22."""
    from bourbaki.cardinaux import ensembles_trichotomie_prop1 as P1
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    va = _t(a)
    vh = h_prime(Ro, a, B)
    imgh = E.img(vh)
    Rof = _R_de(Ro)

    # prop1_segment_propre_clos : chaîne d'implications  neq ⇒ ( seg ⇒ ( bo ⇒ ∃x(...) ) )
    #   (loi_deduction bo, puis seg, puis neq ⇒ neq est l'antécédent EXTERNE).
    p1 = P1.prop1_segment_propre_clos(Ro, a, imgh)          # CLOS (chaîne d'impl)
    bo_form = E.est_bien_ordonne(Rof, va)
    seg_form = E.est_segment(imgh, Rof, va)
    neq_form = non(egal(imgh, va))
    seg_pr2 = seg_pr2_h_prime(Ro, a, B)                     # est_segment(pr₂h',Ro,a)  CLOS
    assert seg_pr2.conclusion == seg_form, "seg_pr2 ≠ est_segment(pr₂h',Ro,a)"
    Hbo = N.assume(bo_form)                                 # bo(Ro,a) honnête
    Hneq = N.assume(neq_form)                               # pr₂h' ≠ a (branche)
    # décharger la chaîne : neq (externe), puis seg, puis bo (interne)
    ex_x = N.modus_ponens(Hneq, p1)                         # seg ⇒ ( bo ⇒ ∃x )
    ex_x = N.modus_ponens(seg_pr2, ex_x)                    # bo ⇒ ∃x
    ex_x = N.modus_ponens(Hbo, ex_x)                        # ∃x( petit ∧ pr₂h'=seg )

    # per-témoin x : ( petit ∧ pr₂h'=seg(Ro,a,x) ) ⊢ ( x∈a et pr₂h'=seg(Ro,a,x) )
    DmD = E.difference(va, imgh)
    petit_x = E.est_plus_petit_element(Rof, DmD, var("x"), x="w")
    eq_x = egal(imgh, seg(Ro, va, var("x")))
    corps_x = et(petit_x, eq_x)
    Hx = N.assume(corps_x)
    petit = conjonction_elim_gauche(Hx)                     # est_plus_petit(Ro,a∖pr₂h',x)
    eq_seg = conjonction_elim_droite(Hx)                    # pr₂h'=seg(Ro,a,x)
    x_in_diff = conjonction_elim_gauche(petit)              # x∈a∖pr₂h'
    # x∈a∖pr₂h' ⇒ x∈a (AXIOME_DIFF)
    ax_diff = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    diff_ssi = instancie(instancie(instancie(ax_diff, va), imgh), var("x"))
    x_split = N.modus_ponens(x_in_diff, equivalence_avant(diff_ssi))   # x∈a et ¬(x∈pr₂h')
    x_in_a = conjonction_elim_gauche(x_split)               # x∈a
    # cible per-témoin : ( x∈a et pr₂h'=seg(Ro,a,x) )
    corps_cible = conjonction_intro(x_in_a, eq_seg)
    body_ex = et(appartient(var("x"), va), egal(imgh, seg(Ro, va, var("x"))))
    assert corps_cible.conclusion == body_ex, "corps per-témoin mal formé"
    # introduire (∃t)  — binder « x » (le binder du témoin de prop1)
    ex_intro = N.modus_ponens(corps_cible, N.s5(body_ex, var("x"), "x"))
    wit_imp = N.loi_deduction(corps_x, ex_intro)
    res = N.modus_ponens(ex_x, existe_elimination(wit_imp, "x"))   # ∃t(t∈a et pr₂h'=seg(Ro,a,t))
    return res


def pr2_eq_seg_exists_cible(Ro="Ro", a="asr", B="Bsr"):
    """ÉNONCÉ-cible (test miroir) : (∃t)( t∈a et pr₂h' = seg(Ro,a,t) )  [binder « x »]."""
    va = _t(a)
    vh = h_prime(Ro, a, B)
    imgh = E.img(vh)
    return existe("x", et(appartient(var("x"), va), egal(imgh, seg(Ro, va, var("x")))))


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE per-B : (∃t)( t∈a et Eq(B, seg(Ro,a,t)) )  sous {bo,B⊆a,dom h'=B,pr₂h'≠a}.
# ════════════════════════════════════════════════════════════════════════════
def realise_segment_pour_B(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a),  B⊆a,  dom h'=B,  pr₂h'≠a }
            ⊢ (∃t)( t∈a  et  Eq( B , seg(Ro,a,t) ) ).

    🎯 Compose Eq(B,pr₂h') (eq_B_pr2_sous_dom_eq_B, branche dom h'=B) et pr₂h'=seg(Ro,a,t)
    (pr2_eq_seg_exists, branche pr₂h'≠a) : pour le témoin t, pr₂h'=seg(Ro,a,t) réécrit
    (Leibniz) Eq(B,pr₂h') en Eq(B,seg(Ro,a,t)).  C'est la conclusion de subset_realise_
    segment POUR CE B, sous le bon ordre + les 2 conditions de branche.  theorie=22."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    va = _t(a)
    vB = _t(B)
    vh = h_prime(Ro, a, B)
    imgh = E.img(vh)

    eq_Bpr2 = eq_B_pr2_sous_dom_eq_B(Ro, a, B)              # Eq(B,pr₂h')  [bo,B⊆a,dom=B]
    ex_seg = pr2_eq_seg_exists(Ro, a, B)                    # ∃t(t∈a et pr₂h'=seg)  [bo,pr₂h'≠a]

    # per-témoin t : ( t∈a et pr₂h'=seg(Ro,a,t) ) ⊢ ( t∈a et Eq(B,seg(Ro,a,t)) )
    vt = var("x")
    segt = seg(Ro, va, vt)
    corps_t = et(appartient(vt, va), egal(imgh, segt))
    Ht = N.assume(corps_t)
    t_in_a = conjonction_elim_gauche(Ht)
    eq_pr2_seg = conjonction_elim_droite(Ht)                # pr₂h'=seg(Ro,a,t)
    # réécrire pr₂h' → seg(Ro,a,t) dans Eq(B,pr₂h')
    eq_Bseg = _leib(imgh, segt, eq_pr2_seg, lambda w: equipotent(vB, w), eq_Bpr2)  # Eq(B,seg)
    corps_cible = conjonction_intro(t_in_a, eq_Bseg)
    body_ex = et(appartient(vt, va), equipotent(vB, segt))
    assert corps_cible.conclusion == body_ex, "corps per-témoin (Eq) mal formé"
    ex_intro = N.modus_ponens(corps_cible, N.s5(body_ex, vt, "x"))
    wit_imp = N.loi_deduction(corps_t, ex_intro)
    res = N.modus_ponens(ex_seg, existe_elimination(wit_imp, "x"))   # ∃t(t∈a et Eq(B,seg))
    return res


def realise_segment_pour_B_cible(Ro="Ro", a="asr", B="Bsr"):
    """ÉNONCÉ-cible (test miroir) : (∃t)( t∈a et Eq( B , seg(Ro,a,t) ) )  [binder « x »]."""
    va, vB = _t(a), _t(B)
    return existe("x", et(appartient(var("x"), va),
                          equipotent(vB, seg(Ro, va, var("x")))))


# ════════════════════════════════════════════════════════════════════════════
#  RÉDUCTION : dom h'=B DÉCHARGÉ via maximalité + ¬(pr₂h'=a)  (cas / ex falso).
# ════════════════════════════════════════════════════════════════════════════
def dom_eq_B_depuis_branche(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a), B⊆a, ¬(pr₂h'=a) } ⊢ dom h' = B.

    🎯 La MAXIMALITÉ donne ( dom h'=B ) ou ( pr₂h'=a ) (maximalite_h_prime, sous {bo,B⊆a}).
    Sous ¬(pr₂h'=a), l'analyse de cas (cas) : branche pr₂h'=a ⇒ ex falso ⇒ dom h'=B ;
    branche dom h'=B ⇒ direct.  theorie=22."""
    from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
    vh = h_prime(Ro, a, B)
    domh, imgh = E.dom(vh), E.img(vh)
    vB, va = _t(B), _t(a)
    dom_eq_B = egal(domh, vB)
    pr2_eq_a = egal(imgh, va)

    mx = maximalite_h_prime(Ro, a, B)            # ( dom h'=B ) ou ( pr₂h'=a )   [bo, B⊆a]
    assert mx.conclusion == ou(dom_eq_B, pr2_eq_a), "maximalité mal formée"
    Hneq = N.assume(non(pr2_eq_a))               # ¬(pr₂h'=a)  (branche)
    # branche A : dom h'=B ⇒ dom h'=B
    brA = a_implique_a(dom_eq_B)
    # branche B : pr₂h'=a ⇒ dom h'=B  (ex falso : pr₂h'=a contre ¬(pr₂h'=a))
    HB = N.assume(pr2_eq_a)
    falso = N.modus_ponens(HB, N.modus_ponens(Hneq, N.s2(non(pr2_eq_a), dom_eq_B)))
    brB = N.loi_deduction(pr2_eq_a, falso)       # pr₂h'=a ⇒ dom h'=B
    res = cas(mx, brA, brB)                      # dom h'=B  [bo, B⊆a, ¬(pr₂h'=a)]
    assert res.conclusion == dom_eq_B, "conclusion ≠ dom h'=B"
    return res


def realise_segment_pour_B_sans_dom(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a),  B⊆a,  ¬(pr₂h'=a) }
            ⊢ (∃t)( t∈a  et  Eq( B , seg(Ro,a,t) ) ).

    🎯 `realise_segment_pour_B` avec dom h'=B DÉCHARGÉ par dom_eq_B_depuis_branche
    (maximalité + ¬(pr₂h'=a)).  L'hypothèse pr₂h'≠a SUBSUME dom h'=B (via maximalité) :
    il ne reste que { bo(Ro,a), B⊆a, pr₂h'≠a }.  theorie=22, NON vacueux.

    Ainsi `subset_realise_segment` POUR CE B est CLOS aux SEULES honnêtes { bo(Ro,a),
    B⊆a, pr₂h'≠a }, où pr₂h'≠a EST la condition « B n'épuise pas a » (B est order-iso
    à un segment PROPRE de a ssi pr₂h'≠a)."""
    base = realise_segment_pour_B(Ro, a, B)      # [B⊆a, dom h'=B, pr₂h'≠a, bo(Ro,a)]
    vh = h_prime(Ro, a, B)
    dom_eq_B = egal(E.dom(vh), _t(B))
    dom_proof = dom_eq_B_depuis_branche(Ro, a, B)   # [bo, B⊆a, ¬(pr₂h'=a)] ⊢ dom h'=B
    res = N.modus_ponens(dom_proof, N.loi_deduction(dom_eq_B, base))
    assert res.conclusion == realise_segment_pour_B_cible(Ro, a, B)
    return res


__all__ = [
    "h_prime", "iso_h_prime", "func_h_prime", "maximalite_h_prime",
    "seg_dom_h_prime", "seg_pr2_h_prime",
    "eq_B_pr2_sous_dom_eq_B", "eq_B_pr2_sous_dom_eq_B_cible",
    "pr2_eq_seg_exists", "pr2_eq_seg_exists_cible",
    "realise_segment_pour_B", "realise_segment_pour_B_cible",
    "dom_eq_B_depuis_branche", "realise_segment_pour_B_sans_dom",
    "equipotent_implique_inf_egal",
    "pr2_eq_a_donne_eq_B_a", "realise_segment_pour_B_clean",
    "realise_segment_pour_B_clean_cible",
]


# ════════════════════════════════════════════════════════════════════════════
#  ✅ equipotent(X,Y) ⇒ X≤Y  — une bijection est une injection.  (CLOS, theorie=22.)
# ════════════════════════════════════════════════════════════════════════════
def equipotent_implique_inf_egal(X="X", Y="Y"):
    """⊢ equipotent(X,Y) ⇒ inf_egal_card(X,Y).   CLOS, 0 hypothèse.

    Une bijection F:X→Y est une injection : est_bijection_de(F,X,Y) =
    (func∧dom=X)∧injective_dans(F,X)∧image(F,X)=Y ; de image(F,X)=Y on tire
    image(F,X)⊆Y (Leibniz sur image⊆image réflexif), d'où est_injection_de(F,X,Y),
    puis (∃F) = inf_egal_card(X,Y) ; ∃-élim du témoin de bijection.  theorie=22."""
    from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    from bourbaki.cardinaux.ensembles_cardinaux import (
        est_bijection_de, est_injection_de, inf_egal_card,
    )
    vX, vY, vF = _t(X), _t(Y), var("F")
    bij = est_bijection_de(vF, vX, vY)
    img = E.image(vF, vX)
    Hb = N.assume(bij)
    func_dom = conjonction_elim_gauche(Hb)              # func∧dom=X
    bijective = conjonction_elim_droite(Hb)             # injective_dans∧image=Y
    inj_dans = conjonction_elim_gauche(bijective)       # injective_dans(F,X)
    img_eq = conjonction_elim_droite(bijective)         # image(F,X)=Y
    # image(F,X)⊆Y : Leibniz (image=Y) sur image⊆image (réflexif)
    incl_II = N.generalisation("z", a_implique_a(appartient(var("z"), img)))   # image⊆image
    incl_iY = _leib(img, vY, img_eq, lambda w: inclus(img, w), incl_II)        # image⊆Y
    inj = conjonction_intro(conjonction_intro(func_dom, inj_dans), incl_iY)
    assert inj.conclusion == est_injection_de(vF, vX, vY), "recompose injection KO"
    le = N.modus_ponens(inj, N.s5(est_injection_de(var("F"), vX, vY), vF, "F"))  # inf_egal_card
    return existe_elimination(N.loi_deduction(bij, le), "F")   # equipotent ⇒ inf_egal


# ════════════════════════════════════════════════════════════════════════════
#  pr₂h'=a  ⇒  Eq(B,a)   (donc ¬Eq(B,a) ⇒ ¬(pr₂h'=a) : branche éliminée par B≁a).
# ════════════════════════════════════════════════════════════════════════════
def pr2_eq_a_donne_eq_B_a(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a), B⊆a, pr₂h'=a } ⊢ Eq(B, a).

    🎯 Si pr₂h'=a, l'iso h' (de dom h' sur pr₂h'=a) AUGMENTÉ de func/dom donne
    Eq(dom h', a) (iso_implique_equipotent) ; donc a≤dom h' (equipotent_implique_inf_egal
    sur Eq(a,dom h') = sym), dom h'⊆B (seg_dom_h_prime ⇒ 1ᵉʳ conjoint) ⇒ dom h'≤B ⇒
    a≤B (transitivité) ; B⊆a ⇒ B≤a ; CANTOR-BERNSTEIN ⇒ Eq(B,a).  theorie=22.

    CONSÉQUENCE (contraposée) : ¬Eq(B,a) ⇒ ¬(pr₂h'=a) — la condition de branche
    ¬(pr₂h'=a) de realise_segment_pour_B_sans_dom est IMPLIQUÉE par « B n'est pas
    équipotent à a », i.e. B est strictement « plus court » que a."""
    from bourbaki.cardinaux.ensembles_cantor_bernstein_final._recollement import cantor_bernstein
    from bourbaki.cardinaux.ensembles_clause_plus_petit_correspondance import inf_egal_card_de_inclus
    from bourbaki.cardinaux.ensembles_cardinaux_consequences import _inf_egal_transitive_t
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent as _eq
    va, vB = _t(a), _t(B)
    vh = h_prime(Ro, a, B)
    domh, imgh = E.dom(vh), E.img(vh)
    Rind_f = OI.Rind(Ro, B)
    Rof = _R_de(Ro)

    iso = iso_h_prime(Ro, a, B)                 # est_iso(h', dom h', pr₂h', Rind, Ro, x, w)
    func = func_h_prime(Ro, a, B)               # est_fonctionnel(h')
    H_pr2 = N.assume(egal(imgh, va))            # pr₂h' = a

    # réécrire pr₂h' → a dans l'iso (Leibniz) : est_iso(h', dom h', a, Rind, Ro)
    iso_a = _leib(imgh, va, H_pr2,
                  lambda w: V.est_isomorphisme_ordre(vh, domh, w, Rind_f, Rof, x="x", y="w"),
                  iso)
    # iso_implique_equipotent(h', dom h', a, Rind, Ro, x, w) : Eq(dom h', a)
    iie = RSC.iso_implique_equipotent(f=vh, X=domh, Y=va, R=OI.graphe_induit(Ro, B),
                                      Rp=_t(Ro), x="x", y="w")
    triple = conjonction_intro(conjonction_intro(iso_a, func), N.reflexivite(domh))
    eq_dom_a = N.modus_ponens(triple, iie)      # Eq(dom h', a)

    # a ≤ dom h' :  Eq(dom h',a) ⇒ Eq(a,dom h') (sym) ⇒ a ≤ dom h'
    eq_a_dom = _eq_symetrie(domh, va, eq_dom_a)            # Eq(a, dom h')
    a_le_dom = N.modus_ponens(eq_a_dom, equipotent_implique_inf_egal(va, domh))   # a ≤ dom h'

    # dom h' ⊆ B  (1ᵉʳ conjoint de est_segment(dom h',Rind,B))
    seg_dom = seg_dom_h_prime(Ro, a, B)         # est_segment(dom h', Rind, B)
    dom_sub_B = conjonction_elim_gauche(seg_dom)   # dom h' ⊆ B
    dom_le_B = N.modus_ponens(dom_sub_B, inf_egal_card_de_inclus(domh, vB))   # dom h' ≤ B

    # a ≤ B  (transitivité : a ≤ dom h' ≤ B)
    trans = _inf_egal_transitive_t(va, domh, vB)   # (a≤dom h' et dom h'≤B) ⇒ a≤B
    a_le_B = N.modus_ponens(conjonction_intro(a_le_dom, dom_le_B), trans)     # a ≤ B

    # B ≤ a  (B⊆a)
    H_B_sub = N.assume(inclus(vB, va))          # B⊆a (honnête)
    B_le_a = N.modus_ponens(H_B_sub, inf_egal_card_de_inclus(vB, va))         # B ≤ a

    # CANTOR-BERNSTEIN : (B≤a et a≤B) ⇒ Eq(B,a)
    #   ⚠️ passer les NOMS (B,a) et non var(...) : cantor_bernstein gère ses binders
    #   internes f,g,D via les NOMS de ses arguments (sinon collision Leibniz).
    Bn = B if isinstance(B, str) else B.nom
    an = a if isinstance(a, str) else a.nom
    cb = cantor_bernstein(Bn, an)               # (B≤a et a≤B) ⇒ Eq(B,a)
    eq_Ba = N.modus_ponens(conjonction_intro(B_le_a, a_le_B), cb)             # Eq(B, a)
    assert eq_Ba.conclusion == _eq(vB, va), "conclusion ≠ Eq(B,a)"
    return eq_Ba


def _eq_symetrie(X, Y, h_eq_XY):
    """De ⊢ Eq(X,Y) [h_eq_XY] déduit ⊢ Eq(Y,X).  (symétrie de l'équipotence, dépôt.)"""
    from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotence_symetrique
    imp = equipotence_symetrique(f="F", x=_t(X), y=_t(Y))   # Eq(X,Y) ⇒ Eq(Y,X)
    return N.modus_ponens(h_eq_XY, imp)


def realise_segment_pour_B_clean(Ro="Ro", a="asr", B="Bsr"):
    """⊢ { bo(Ro,a),  B⊆a,  ¬Eq(B,a) }
            ⊢ (∃t)( t∈a  et  Eq( B , seg(Ro,a,t) ) ).

    🎯🎯 LA FORME PROPRE/INTERPRÉTABLE — la condition de branche opaque ¬(pr₂h'=a) est
    REMPLACÉE par la condition CARDINALE HONNÊTE `¬Eq(B,a)` (« B n'est pas équipotent à
    a », i.e. B strictement plus court).  Via pr2_eq_a_donne_eq_B_a (pr₂h'=a ⇒ Eq(B,a))
    contraposé : ¬Eq(B,a) ⇒ ¬(pr₂h'=a), qui décharge la condition de
    realise_segment_pour_B_sans_dom.  theorie=22, NON vacueux.

    C'est subset_realise_segment RESTREINT aux B avec ¬Eq(B,a) — la forme VRAIE et
    CLOSE.  (Le cas Eq(B,a), notamment B=a, est précisément l'exception où aucun
    segment PROPRE ne convient.)"""
    from bourbaki.cardinaux.ensembles_cardinaux import equipotent as _eq
    from bourbaki.logique.tactiques.tactiques_abrege2 import contraposition
    va, vB = _t(a), _t(B)
    vh = h_prime(Ro, a, B)
    imgh = E.img(vh)
    pr2_eq_a = egal(imgh, va)

    # pr₂h'=a ⇒ Eq(B,a)  ; contraposée : ¬Eq(B,a) ⇒ ¬(pr₂h'=a)
    bridge = pr2_eq_a_donne_eq_B_a(Ro, a, B)              # [bo, B⊆a, pr₂h'=a] ⊢ Eq(B,a)
    imp_bridge = N.loi_deduction(pr2_eq_a, bridge)        # [bo, B⊆a] ⊢ pr₂h'=a ⇒ Eq(B,a)
    contra = contraposition(imp_bridge)                  # ¬Eq(B,a) ⇒ ¬(pr₂h'=a)  [bo, B⊆a]
    H_neq_eq = N.assume(non(_eq(vB, va)))                 # ¬Eq(B,a) (honnête)
    not_pr2_eq_a = N.modus_ponens(H_neq_eq, contra)       # ¬(pr₂h'=a)  [bo, B⊆a, ¬Eq(B,a)]

    base = realise_segment_pour_B_sans_dom(Ro, a, B)      # [bo, B⊆a, ¬(pr₂h'=a)]
    res = N.modus_ponens(not_pr2_eq_a, N.loi_deduction(non(pr2_eq_a), base))
    assert res.conclusion == realise_segment_pour_B_cible(Ro, a, B)
    return res


def realise_segment_pour_B_clean_cible(Ro="Ro", a="asr", B="Bsr"):
    """ÉNONCÉ-cible (test miroir) : (∃t)( t∈a et Eq( B , seg(Ro,a,t) ) )."""
    return realise_segment_pour_B_cible(Ro, a, B)
