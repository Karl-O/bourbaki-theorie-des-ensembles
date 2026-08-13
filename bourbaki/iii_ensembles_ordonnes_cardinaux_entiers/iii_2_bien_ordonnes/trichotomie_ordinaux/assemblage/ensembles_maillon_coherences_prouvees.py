"""§III.2 — Théorème 3 (TRICHOTOMIE) : le MAILLON FINAL avec ses 3 COHÉRENCES PROUVÉES.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `maillon_final_h_plus` (ensembles_trichotomie_maillon_final) réduit la
trichotomie à 6 hypothèses : les 3 COHÉRENCES de h=h_iso_max
    [0] compatibilite_inverse_h   (∀u,v,u')( ((u,v)∈h et (u',v)∈h) ⇒ u=u' )
    [2] est_fonctionnel(h)        (∀u,v,z)( ((u,v)∈h et (u,z)∈h) ⇒ v=z )
    [4] compatibilite_ordre_h     (∀u,v,u',v')( ((u,v)∈h et (u',v')∈h) ⇒ (R{u,u'}⇔Rp{v,v'}) )
plus la MAXIMALITÉ [5] (dom h=E ∨ pr₂ h=F) et les 2 SEGMENTS [1],[3] (dom h, pr₂ h).

`maillon_final_h_plus2` décharge [0],[2],[4] sur les « TÉMOINS COMMUNS » (encore REPORTÉS,
Lemme 1 §III.2).  ICI on va plus loin : les 3 cohérences sont DÉCHARGÉES sur leurs
PREUVES (sous les SEULES hypothèses HONNÊTES {bo(R,E), bo(R',F), residu_univ_app}) :

  • compatibilite_inverse_h_prouve / compatibilite_ordre_h_prouve  (ensembles_h_bien_defini,
    DÉJÀ PROUVÉES — chacune ⊢ sa formule sous {bo,bo,residu} via la COÏNCIDENCE CLOSE) ;
  • `fonctionnel_h_prouve` (LIVRÉ ICI) : ⊢ est_fonctionnel(h) sous {bo,bo,residu}, miroir
    EXACT de compatibilite_inverse_h_prouve, via la FUSION (fusion_depuis_coincidence_app,
    dérivée de coincidence_univ_app CLOS) en COLLAPSANT le second antécédent (u'→u) puis
    en AFFAIBLISSANT temoin_commun_h(u,v,u,z) → temoin_commun_fonc_h(u,v,z).

CE MODULE LIVRE (theorie=22, rien postulé — NE MODIFIE AUCUN fichier existant) :

  ✅ `fonctionnel_h_prouve(...)` :
        { bo(R,E), bo(R',F), residu_univ_app } ⊢ est_fonctionnel(h).
     CONCLUSION == `fonctionnel_depuis_temoin_cible` (= E.est_fonctionnel(h)), LITTÉRALEMENT.

  ✅ `maillon_final_h_plus3(...)` :
        { bo(R,E), bo(R',F), residu_univ_app,
          (dom h=E ∨ pr₂ h=F),  est_segment(dom h,R,E),  est_segment(pr₂ h,Rp,F) }
            ⊢ trichotomie_ordinaux_canon(E,R,F,Rp)  (== maillon_final_cible).
     Les 3 cohérences/témoins SONT REMPLACÉS par {bo,bo,residu} : il ne reste que la
     MAXIMALITÉ + les 2 SEGMENTS + l'arrière-plan structurel HONNÊTE.

────────────────────────────────────────────────────────────────────────────────
⚠️ CONTRAINTE DE NOMMAGE (héritée de coincidence_univ_app / fusion_depuis_coincidence_app).
La coïncidence/fusion PROUVÉE est un SCHÉMA sur F,R,R' avec l'ambiant E HARDCODÉ « E ».
Les noms AMBIANTS restent CANONIQUES : E_set="E", F_set="F", R="R", Rp="Rp".

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  NON vacueux : est_fonctionnel(h)
n'est aucune de ses hypothèses (≠ bo, ≠ résidu).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, appartient,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences import ensembles_trichotomie_coherences as COH
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.temoins_comparabilite import ensembles_temoin_deux_couples as T2
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.coincidence_fusion import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences import ensembles_h_bien_defini as HBD
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_maillon_final as MF
import bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences.ensembles_trichotomie_h_iso as HI


# ── noms-témoins INTERNES imposés par fusion_depuis_coincidence_app (hardcodés) ──
_UA, _VA, _UB, _VB = "ua", "va", "ub", "vb"
_S, _T, _PHI = "S", "T", "phi"
_HOLE = "hole_mcp"


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b et ⊢ Φ[a] déduit ⊢ Φ[b]   (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# `equivalence_avant` est utilisé par _leib (S6 produit ⇔) — import paresseux local.
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import equivalence_avant  # noqa: E402


def _renommer_quantificateurs(thm, noms_cibles):
    """Renomme les n quantificateurs ∀ EXTERNES de thm (outer→inner) vers noms_cibles,
    par instanciation puis re-généralisation.  SÛR (aucun artefact « @ ») LORSQUE le corps
    quantifié ne porte AUCUN liant interne homonyme des noms_cibles — c'est le cas ici :
    le corps est ( (·,·)∈h et (·,·)∈h ) ⇒ (=) avec h OPAQUE (terme app, axiome NON déplié).
    Identique à `HBD._renommer_quantificateurs`."""
    out = thm
    for c in noms_cibles:                      # instancier outer→inner
        out = instancie(out, var(c))
    for c in reversed(noms_cibles):            # re-généraliser (dernier = outer)
        out = N.generalisation(c, out)
    return out


# ════════════════════════════════════════════════════════════════════════════
#  TÉMOIN FONCTIONNEL PROUVÉ sous { bo(R,E), bo(R',F), residu_univ_app }.
#  La FUSION prouvée donne temoin_commun_h(ua,va,ub,vb) ; on COLLAPSE le second
#  antécédent (ub→ua) → temoin_commun_h(ua,va,ua,vb), puis on AFFAIBLIT le corps
#  existentiel (drop du 2ᵉ « ua∈S » dupliqué) → temoin_commun_fonc_h(ua,va,vb).
# ════════════════════════════════════════════════════════════════════════════
def _temoin_fonc_prouve():
    """⊢ { (ua,va)∈h, (ua,vb)∈h, bo(R,E), bo(R',F), residu_univ_app }
          ⊢ temoin_commun_fonc_h(ua,va,vb).

    Côté FONCTIONNALITÉ (deux valeurs va,vb du MÊME antécédent ua).  La FUSION prouvée
    (`fusion_depuis_coincidence_app`, dérivée de la COÏNCIDENCE CLOSE) donne
    fusion_hyp(ua,va,ub,vb) ; on GÉNÉRALISE ub (NON libre dans ses hypothèses {bo,bo,
    residu}) puis on INSTANCIE ub→ua (ua n'est liant nulle part dans fusion_hyp ⇒ aucun
    « @ »), obtenant fusion_hyp(ua,va,ua,vb).  `temoin_commun_depuis_deux_h_couples`
    (u=ua,v=va,up=ua,vp=vb) décharge cette fusion via les deux couples (ua,va)∈h,
    (ua,vb)∈h ⇒ temoin_commun_h(ua,va,ua,vb).  Enfin on AFFAIBLIT le CŒUR existentiel
    (le 2ᵉ « ua∈S » est REDONDANT) → temoin_commun_fonc_h(ua,va,vb), remonté à travers
    les 3 ∃ (S,T,φ) par `monotonie_existe`.

    Le 4ᵉ point n'est PAS collapsé (côté fonc : c'est le PREMIER antécédent qui collapse,
    là où le côté inverse — _temoin_inv_prouve — collapse le 4ᵉ point vb→va)."""
    # ── FUSION prouvée + COLLAPSE ub→ua : fusion_hyp(ua,va,ua,vb)  [hyps : bo,bo,residu] ──
    fus = FDA.fusion_depuis_coincidence_app()                   # fusion_hyp(ua,va,ub,vb)
    fus_c = instancie(N.generalisation(_UB, fus), var(_UA))     # fusion_hyp(ua,va,ua,vb)
    fhc_form = T2.fusion_hyp("E", "R", "F", "Rp",
                             u=_UA, v=_VA, up=_UA, vp=_VB, S=_S, T=_T, phi=_PHI)
    assert fus_c.conclusion == fhc_form, "fusion_hyp(ua,va,ua,vb) ≠ collapse de la fusion prouvée"

    # ── DÉCHARGE de la fusion → temoin_commun_h(ua,va,ua,vb)  [hyps : couples, bo,bo,residu] ──
    tch = T2.temoin_commun_depuis_deux_h_couples("E", "R", "F", "Rp",
                                                 u=_UA, v=_VA, up=_UA, vp=_VB,
                                                 S=_S, T=_T, phi=_PHI)
    tcomm = N.modus_ponens(fus_c, N.loi_deduction(fhc_form, tch))   # temoin_commun_h(ua,va,ua,vb)

    # ── AFFAIBLISSEMENT du CŒUR : temoin_commun_h(ua,va,ua,vb) ⇒ temoin_commun_fonc_h(ua,va,vb) ──
    #   collapsed ordre coeur = (((((seg,seg,iso),ua∈S),ua∈S),va=φ(ua)),vb=φ(ua))   [7 conjoints]
    #   fonc coeur            = ((((seg,seg,iso),ua∈S),va=φ(ua)),vb=φ(ua))           [6 conjoints]
    #   ⇒ on DROP le 2ᵉ « ua∈S » dupliqué.
    coeur_ord = COH._temoin_commun_coeur("E", "R", "F", "Rp", _UA, _VA, _UA, _VB, _S, _T, _PHI)
    fonc_form = COH._temoin_fonc_coeur("E", "R", "F", "Rp", _UA, _VA, _VB, _S, _T, _PHI)
    Hc = N.assume(coeur_ord)
    c_vbphi = conjonction_elim_droite(Hc)          # vb=φ(ua)
    c0 = conjonction_elim_gauche(Hc)               # …,ua∈S, ua∈S, va=φ(ua)
    c_vaphi = conjonction_elim_droite(c0)          # va=φ(ua)
    c1 = conjonction_elim_gauche(c0)               # …,ua∈S, ua∈S
    c2 = conjonction_elim_gauche(c1)               # (seg,seg,iso), ua∈S   (1er « ua∈S » conservé)
    fonc_proof = conjonction_intro(conjonction_intro(c2, c_vaphi), c_vbphi)
    assert fonc_proof.conclusion == fonc_form, "affaiblissement ≠ cœur de temoin_commun_fonc_h"
    imp_coeur = N.loi_deduction(coeur_ord, fonc_proof)    # coeur_ord ⇒ coeur_fonc
    # remonter à travers les 3 ∃ : temoin_commun_h(ua,va,ua,vb) ⇒ temoin_commun_fonc_h(ua,va,vb)
    imp_phi = monotonie_existe(imp_coeur, _PHI)
    imp_T = monotonie_existe(imp_phi, _T)
    imp_S = monotonie_existe(imp_T, _S)
    return N.modus_ponens(tcomm, imp_S)            # temoin_commun_fonc_h(ua,va,vb)


# ════════════════════════════════════════════════════════════════════════════
#  TRANSPORT (réutilise verbatim la logique de fonctionnel_depuis_temoin) :
#  du TÉMOIN FONCTIONNEL, dériver l'égalité des deux valeurs sur les points internes.
# ════════════════════════════════════════════════════════════════════════════
def _transport_fonc():
    """⊢ temoin_commun_fonc_h(ua,va,vb) ⇒ va=vb.  (INCONDITIONNEL — transitivité via
    φ(ua), transport identique à `fonctionnel_depuis_temoin`.)"""
    coeur = COH._temoin_fonc_coeur("E", "R", "F", "Rp", _UA, _VA, _VB, _S, _T, _PHI)
    vu, vv, vz = var(_UA), var(_VA), var(_VB)
    vphi = var(_PHI)
    fu = E.valeur(vphi, vu)

    Hc = N.assume(coeur)
    c0 = conjonction_elim_gauche(Hc)               # …et ua∈S et va=φ(ua)
    c_z = conjonction_elim_droite(Hc)              # vb=φ(ua)
    c_v = conjonction_elim_droite(c0)              # va=φ(ua)
    fu_eq_z = N.modus_ponens(c_z, symetrie(vz, fu))            # φ(ua)=vb
    v_eq_z = _leib(fu, vz, fu_eq_z, lambda w: egal(vv, w), c_v)  # va=vb

    body_coeur = N.loi_deduction(coeur, v_eq_z)
    body_phi = existe_elimination(body_coeur, _PHI)
    body_T = existe_elimination(body_phi, _T)
    return existe_elimination(body_T, _S)          # temoin_commun_fonc_h(ua,va,vb) ⇒ va=vb


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 TARGET 1 — est_fonctionnel(h) PROUVÉE.
# ════════════════════════════════════════════════════════════════════════════
def fonctionnel_h_prouve(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ { bo(R,E), bo(R',F), residu_univ_app } ⊢ est_fonctionnel(h).

    🎯🎯 FONCTIONNALITÉ de h (= h_iso_max) PROUVÉE comme THÉORÈME (et NON prise en
    hypothèse comme dans maillon_final_h_plus).  MIROIR EXACT de
    `compatibilite_inverse_h_prouve` (ensembles_h_bien_defini), côté FONCTIONNALITÉ.

    PREUVE.  Pour (ua,va)∈h et (ua,vb)∈h (MÊME antécédent ua) :
      • le TÉMOIN FONCTIONNEL temoin_commun_fonc_h(ua,va,vb) — UN iso φ:S≅T de segments
        avec ua∈S, va=φ(ua)=vb — est PROUVÉ (_temoin_fonc_prouve) : la FUSION
        (fusion_depuis_coincidence_app, dérivée de la COÏNCIDENCE CLOSE coincidence_univ
        _app) le fournit en COLLAPSANT le second antécédent (ub→ua) puis en AFFAIBLISSANT
        temoin_commun_h(ua,va,ua,vb) → temoin_commun_fonc_h(ua,va,vb), sous bo(R,E)+
        bo(R',F)+résidu géométrique ;
      • la TRANSITIVITÉ via φ(ua) (_transport_fonc) donne alors va=vb.
    On recolle la prémisse ((ua,va)∈h et (ua,vb)∈h) ⇒ va=vb, puis on UNIVERSALISE.

    ⚠️ NOMS : le corps est bâti aux noms-témoins internes ua,va,vb (imposés par la
    fusion), puis les QUANTIFICATEURS externes sont renommés vers les liants par DÉFAUT
    u,v,z (corps final = (·,·)∈h avec h opaque ⇒ renommage SANS « @ »).

    theorie=22.  NON vacueux : est_fonctionnel(h) n'est aucune hypothèse (≠ bo, ≠ résidu).
    Hypothèses HONNÊTES (bons ordres ambiants + résidu géométrique, JAMAIS la coïncidence
    — PROUVÉE — ni la cohérence elle-même)."""
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis (schéma coincidence_univ_app)"
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vz = var(_UA), var(_VA), var(_VB)

    tfonc = _temoin_fonc_prouve()                  # ⊢ temoin_commun_fonc_h(ua,va,vb) [bo,bo,res,couples]
    transport = _transport_fonc()                  # temoin_commun_fonc_h(ua,va,vb) ⇒ va=vb
    v_eq_z = N.modus_ponens(tfonc, transport)      # va=vb  [hyps: couples, bo, bo, résidu]

    # recoller la prémisse ((ua,va)∈h et (ua,vb)∈h) ⇒ va=vb
    c1f = appartient(E.couple(vu, vv), h)
    c2f = appartient(E.couple(vu, vz), h)
    prem = et(c1f, c2f)
    Hprem = N.assume(prem)
    res = v_eq_z
    res = N.modus_ponens(conjonction_elim_gauche(Hprem), N.loi_deduction(c1f, res))
    res = N.modus_ponens(conjonction_elim_droite(Hprem), N.loi_deduction(c2f, res))
    body = N.loi_deduction(prem, res)
    full = N.generalisation(_UA, N.generalisation(_VA, N.generalisation(_VB, body)))
    # renommer les 3 quantificateurs externes ua,va,vb → u,v,z (défauts de la cible)
    return _renommer_quantificateurs(full, ["u", "v", "z"])


def fonctionnel_h_prouve_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : est_fonctionnel(h)  (= COH.fonctionnel_depuis_temoin_cible)."""
    return COH.fonctionnel_depuis_temoin_cible(E_set, R, F_set, Rp)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 TARGET 2 — maillon_final_h_plus3 : les 3 cohérences DÉCHARGÉES sur leurs PREUVES.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Demo.3 | E III.21 L.23-38 | PDF p.124  (démonstration du Th. 3 : cohérences de l'iso maximal h, maillon d'assemblage)
def maillon_final_h_plus3(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ { bo(R,E), bo(R',F), residu_univ_app,
           (dom h=E ∨ pr₂ h=F),  est_segment(dom h,R,E),  est_segment(pr₂ h,Rp,F) }
            ⊢ trichotomie_ordinaux_canon(E,R,F,Rp).

    🎯🎯 `maillon_final_h_plus` (6 hypothèses) avec ses 3 COHÉRENCES de h DÉCHARGÉES sur
    leurs PREUVES — et NON, comme `maillon_final_h_plus2`, sur les « TÉMOINS COMMUNS »
    (qui restaient REPORTÉS).  Les 3 cohérences
        compatibilite_inverse_h,  est_fonctionnel(h),  compatibilite_ordre_h
    sont REMPLACÉES par les SEULES hypothèses HONNÊTES {bo(R,E), bo(R',F), residu_univ_app}
    (chaque preuve les porte) :
        • compatibilite_inverse_h  ← HBD.compatibilite_inverse_h_prouve  (PROUVÉE) ;
        • compatibilite_ordre_h    ← HBD.compatibilite_ordre_h_prouve    (PROUVÉE) ;
        • est_fonctionnel(h)       ← fonctionnel_h_prouve                (LIVRÉE ICI).

    Le séquent FINAL ne porte donc QUE : {bo,bo,residu} (arrière-plan structurel honnête,
    JAMAIS la coïncidence — PROUVÉE) + la MAXIMALITÉ (dom h=E ∨ pr₂ h=F) + les 2 SEGMENTS
    (dom h, pr₂ h).  Les 3 témoins/cohérences ont DISPARU.  Conclusion == maillon_final_cible.

    Le pattern de décharge est `MF._decharge(mf, hyp_form, preuve)` GARDÉ par
    `preuve.conclusion == hyp_form ∈ mf.hypotheses` (identique à maillon_final_h_plus2).
    theorie=22, rien postulé."""
    mf = MF.maillon_final_h_plus(E_set, R, F_set, Rp)
    # PREUVES des 3 cohérences (chacune sous {bo,bo,residu})
    paires = [
        (HI.compatibilite_inverse_h(E_set, R, F_set, Rp),
         HBD.compatibilite_inverse_h_prouve(E_set, R, F_set, Rp)),
        (HI.compatibilite_ordre_h(E_set, R, F_set, Rp),
         HBD.compatibilite_ordre_h_prouve(E_set, R, F_set, Rp)),
        (fonctionnel_h_prouve_cible(E_set, R, F_set, Rp),
         fonctionnel_h_prouve(E_set, R, F_set, Rp)),
    ]
    for hyp_form, preuve in paires:
        if hyp_form in set(mf.hypotheses) and preuve.conclusion == hyp_form:
            mf = MF._decharge(mf, hyp_form, preuve)
    return mf


def maillon_final_h_plus3_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : trichotomie_ordinaux_canon(E,R,F,Rp) (== maillon_final_cible)."""
    return MF.maillon_final_cible(E_set, R, F_set, Rp)


def maillon_final_h_plus3_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 5 HYPOTHÈSES SURVIVANTES ATTENDUES (documentation / test miroir) :
       les 2 HONNÊTES de la fusion {bo(R,E), bo(R',F)}  (residu_univ_app ÉLIMINÉ)
       + maximalité (dom h=E ∨ pr₂ h=F) + les 2 segments (dom h, pr₂ h).

    Les 2 SEGMENTS et la MAXIMALITÉ sont EXTRAITS de `maillon_final_h_plus` (source
    CANONIQUE — mêmes binders xo/yo de est_segment, mêmes côtés du « ou »), pour éviter
    toute divergence de nommage de liants.  Concrètement = les hypothèses de
    `maillon_final_h_plus` PRIVÉES des 3 cohérences, AUGMENTÉES des 2 honnêtes."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    honnetes = FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp)
    coherences = {
        HI.compatibilite_inverse_h(E_set, R, F_set, Rp),
        HI.compatibilite_ordre_h(E_set, R, F_set, Rp),
        E.est_fonctionnel(h),
    }
    mf = MF.maillon_final_h_plus(E_set, R, F_set, Rp)
    restantes = [x for x in mf.hypotheses if x not in coherences]   # maximalité + 2 segments
    return honnetes + restantes


__all__ = [
    "fonctionnel_h_prouve", "fonctionnel_h_prouve_cible",
    "maillon_final_h_plus3", "maillon_final_h_plus3_cible",
    "maillon_final_h_plus3_hypotheses",
]
