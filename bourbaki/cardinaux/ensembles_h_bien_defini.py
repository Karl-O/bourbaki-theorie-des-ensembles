"""§III.2 — Théorème 3 (TRICHOTOMIE) : les deux COHÉRENCES de h (=h_iso_max) PROUVÉES.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `ensembles_trichotomie_h_iso` POSE en HYPOTHÈSES EXPLICITES les deux formules
de cohérence (« bonne-définition » de h) :

    (A)  compatibilite_inverse_h := (∀u)(∀v)(∀u')( ((u,v)∈h et (u',v)∈h) ⇒ u=u' )
    (B)  compatibilite_ordre_h   := (∀u)(∀v)(∀u')(∀v')(
              ((u,v)∈h et (u',v')∈h) ⇒ (R{u,u'} ⇔ Rp{v,v'}) )

Elles encapsulent l'INJECTIVITÉ par couples (A) et la COMPATIBILITÉ D'ORDRE par
couples (B) de l'iso maximal h.  Ce module les PROUVE comme THÉORÈMES, en assemblant
DEUX briques DÉJÀ CLOSES côté Lemme 1 §III.2 (coïncidence des isos de segments) :

  • `fusion_depuis_coincidence_app` (ensembles_fusion_depuis_coincidence_app) :
        { bo(R,E), bo(R',F) } ⊢ fusion_hyp(u,v,u',v')
    — la FUSION (deux couples de h sont couverts par UN iso commun de segments)
      DÉRIVÉE de la COÏNCIDENCE PROUVÉE (coincidence_univ_app, THÉORÈME CLOS).  La
      coïncidence du Lemme 1 n'est PLUS postulée ; et le RÉSIDU géométrique
      (residu_univ_app : segment-de-l'image + inclusion-de-graphe) est désormais
      DÉRIVÉ de `residu_univ_app_renforce` (CLOS) — il ne SUBSISTE PLUS.
  • `temoin_commun_depuis_deux_h_couples` / `temoin_inv_depuis_deux_h_couples`
        (ensembles_temoin_deux_couples) : de {(u,v)∈h, (u',v')∈h, fusion_hyp}
      produisent le TÉMOIN COMMUN  temoin_commun_h / temoin_commun_inv_h.
  • la TRANSPORT-LOGIQUE de `ensembles_trichotomie_coherences` (réutilisée
      verbatim) : du témoin commun, dériver  u=u'  [injectivité de l'iso commun] et
      R{u,u'} ⇔ Rp{v,v'}  [compatibilité d'ordre de l'iso commun].

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (PROUVÉ, theorie=22, rien postulé) :

  ✅ compatibilite_inverse_h_prouve(...) :
        { bo(R,E), bo(R',F) } ⊢ compatibilite_inverse_h.   (A)
  ✅ compatibilite_ordre_h_prouve(...) :
        { bo(R,E), bo(R',F) } ⊢ compatibilite_ordre_h.     (B)
     i.e. CONCLUSION == la FORMULE-builder `compatibilite_inverse_h` /
     `compatibilite_ordre_h` de `ensembles_trichotomie_h_iso`, LITTÉRALEMENT (noms de
     liants par DÉFAUT u,v,u'[,v']).

Les 2 hypothèses SURVIVANTES sont des arrière-plans STRUCTURELS HONNÊTES (les deux bons
ordres ambiants) — JAMAIS la coïncidence (PROUVÉE), ni le résidu géométrique (DÉRIVÉ de
residu_univ_app_renforce, CLOS), ni les cohérences elles-mêmes (qui seraient des
tautologies).  C'est l'INVERSE du statut « hypothèse explicite » de
ensembles_trichotomie_h_iso : ces formules sont désormais DÉRIVÉES.

────────────────────────────────────────────────────────────────────────────────
⚠️ CONTRAINTE DE NOMMAGE (héritée de coincidence_univ_app / fusion_depuis_coincidence
_app).  La coïncidence PROUVÉE est un SCHÉMA sur F,R,R' avec l'ambiant E HARDCODÉ « E »
(binders internes non re-renommables).  De plus `fusion_depuis_coincidence_app` fixe ses
points-témoins internes à ua,va,ub,vb.  On bâtit donc le corps de la preuve à ces noms
internes, PUIS on renomme proprement les TROIS/QUATRE quantificateurs EXTERNES vers les
noms par DÉFAUT u,v,u'[,v'] (renommage SANS artefact « @ » : le corps final ne porte
que (·,·)∈h avec h OPAQUE — aucun liant interne u/v/u'/v' à éviter).  Les noms AMBIANTS
restent CANONIQUES : E_set="E", F_set="F", R="R", Rp="Rp".

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  NON vacueux : (A),(B) ne sont
AUCUNE de leurs hypothèses (≠ bo).

NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, equiv, appartient,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_pont_binder import reecrire
from bourbaki.ordre.iii_1_relations_ordre.isomorphismes_ordre.ensembles_valeur_bridge import valeur_j_egal_y
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_coherences as COH
from bourbaki.cardinaux import ensembles_temoin_deux_couples as T2
from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.cardinaux import ensembles_trichotomie_h_iso as H


# ── noms-témoins INTERNES imposés par fusion_depuis_coincidence_app (hardcodés) ──
_UA, _VA, _UB, _VB = "ua", "va", "ub", "vb"
_S, _T, _PHI = "S", "T", "phi"
_HOLE = "hole_hbd"


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b et ⊢ Φ[a] déduit ⊢ Φ[b]   (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _renommer_quantificateurs(thm, noms_internes, noms_cibles):
    """Renomme les n quantificateurs ∀ EXTERNES de thm (liants noms_internes, dans
    l'ordre outer→inner) vers noms_cibles, par instanciation puis re-généralisation.

    SÛR (aucun artefact « @ ») LORSQUE le corps quantifié ne porte AUCUN liant interne
    homonyme des noms_cibles — c'est le cas ici : le corps est
        ( (·,·)∈h et (·,·)∈h ) ⇒ ( = / ⇔ )
    avec h OPAQUE (terme app, axiome NON déplié), donc sans liant u/v/u'/v'."""
    out = thm
    for c in noms_cibles:                      # instancier outer→inner
        out = instancie(out, var(c))
    for c in reversed(noms_cibles):            # re-généraliser (dernier = outer)
        out = N.generalisation(c, out)
    return out


# ════════════════════════════════════════════════════════════════════════════
#  TÉMOINS COMMUNS PROUVÉS sous { bo(R,E), bo(R',F) }.
#  Assemblent fusion_depuis_coincidence_app (CLOS-cond) + temoin_*_depuis_deux_h.
# ════════════════════════════════════════════════════════════════════════════
def _fusion_hyp_prouve():
    """⊢ { bo(R,E), bo(R',F) } ⊢ fusion_hyp(ua,va,ub,vb).

    DÉLÈGUE à fusion_depuis_coincidence_app (noms-témoins ua,va,ub,vb par défaut) :
    la FUSION dérivée de la coïncidence PROUVÉE (coincidence_univ_app CLOS)."""
    return FDA.fusion_depuis_coincidence_app()         # = fusion_hyp(ua,va,ub,vb)


def _temoin_commun_prouve():
    """⊢ { (ua,va)∈h, (ub,vb)∈h, bo(R,E), bo(R',F) }
          ⊢ temoin_commun_h(ua,va,ub,vb).

    temoin_commun_depuis_deux_h_couples assume {couples, fusion_hyp} ; on DÉCHARGE
    fusion_hyp par _fusion_hyp_prouve (⇒ il ne reste que les couples + bo + résidu)."""
    fus = _fusion_hyp_prouve()                          # fusion_hyp(ua,va,ub,vb)
    fh_form = T2.fusion_hyp("E", "R", "F", "Rp",
                            u=_UA, v=_VA, up=_UB, vp=_VB, S=_S, T=_T, phi=_PHI)
    assert fus.conclusion == fh_form, "fusion_hyp ≠ conclusion de la fusion prouvée"
    tch = T2.temoin_commun_depuis_deux_h_couples("E", "R", "F", "Rp",
                                                 u=_UA, v=_VA, up=_UB, vp=_VB,
                                                 S=_S, T=_T, phi=_PHI)
    return N.modus_ponens(fus, N.loi_deduction(fh_form, tch))


def _temoin_inv_prouve():
    """⊢ { (ua,va)∈h, (ub,va)∈h, bo(R,E), bo(R',F) }
          ⊢ temoin_commun_inv_h(ua,va,ub).

    Côté INVERSE (deux antécédents de la MÊME valeur va).  fusion_inv_hyp(ua,va,ub)
    == fusion_hyp(ua,va,ub,va) (le 4ᵉ point COLLAPSÉ sur va) : on l'obtient de la
    fusion prouvée en GÉNÉRALISANT vb (NON libre dans ses hypothèses) puis en
    INSTANCIANT vb→va (va n'est liant nulle part dans fusion_hyp ⇒ aucun « @ »).
    temoin_inv_depuis_deux_h_couples assume {couples, fusion_inv_hyp} ; décharge."""
    fus = _fusion_hyp_prouve()                          # fusion_hyp(ua,va,ub,vb)
    fus_inv = instancie(N.generalisation(_VB, fus), var(_VA))   # fusion_inv_hyp(ua,va,ub)
    fih_form = T2.fusion_inv_hyp("E", "R", "F", "Rp",
                                 u=_UA, v=_VA, up=_UB, S=_S, T=_T, phi=_PHI)
    assert fus_inv.conclusion == fih_form, "fusion_inv_hyp ≠ collapse de la fusion prouvée"
    tinv = T2.temoin_inv_depuis_deux_h_couples("E", "R", "F", "Rp",
                                               u=_UA, v=_VA, up=_UB, S=_S, T=_T, phi=_PHI)
    return N.modus_ponens(fus_inv, N.loi_deduction(fih_form, tinv))


# ════════════════════════════════════════════════════════════════════════════
#  TRANSPORT (réutilisé verbatim de ensembles_trichotomie_coherences) :
#  du TÉMOIN COMMUN, dériver l'implication-transport sur les points internes.
# ════════════════════════════════════════════════════════════════════════════
def _transport_inverse():
    """⊢ temoin_commun_inv_h(ua,va,ub) ⇒ ua=ub.  (INCONDITIONNEL — injectivité de
    l'iso commun, transport identique à compatibilite_inverse_depuis_temoin.)"""
    coeur = COH._temoin_inv_coeur("E", "R", "F", "Rp", _UA, _VA, _UB, _S, _T, _PHI)
    vu, vup = var(_UA), var(_UB)
    vv = var(_VA)
    vphi = var(_PHI)
    fu, fup = E.valeur(vphi, vu), E.valeur(vphi, vup)

    Hc = N.assume(coeur)
    c0 = conjonction_elim_gauche(Hc)               # …et u∈S et u'∈S et v=φ(u)
    c_vup = conjonction_elim_droite(Hc)            # v=φ(u')
    c1 = conjonction_elim_gauche(c0)               # …et u∈S et u'∈S
    c_vu = conjonction_elim_droite(c0)             # v=φ(u)
    c2 = conjonction_elim_gauche(c1)               # …et u∈S
    c_upS = conjonction_elim_droite(c1)            # u'∈S
    c3 = conjonction_elim_gauche(c2)               # segments et iso
    c_uS = conjonction_elim_droite(c2)             # u∈S
    c_iso = conjonction_elim_droite(c3)            # est_isomorphisme_ordre(φ,S,T,R,Rp)
    c_bij = conjonction_elim_gauche(c_iso)         # est_bijective(φ,S,T)
    c_inj = conjonction_elim_gauche(c_bij)         # injective_dans(φ,S)

    fu_eq_v = N.modus_ponens(c_vu, symetrie(vv, fu))                       # φ(u)=v
    fu_eq_fup = _leib(vv, fup, c_vup, lambda w: egal(fu, w), fu_eq_v)      # φ(u)=φ(u')
    inj_inst = instancie(instancie(c_inj, vu), vup)
    u_eq_up = N.modus_ponens(
        conjonction_intro(conjonction_intro(c_uS, c_upS), fu_eq_fup), inj_inst)  # u=u'

    body_coeur = N.loi_deduction(coeur, u_eq_up)
    body_phi = existe_elimination(body_coeur, _PHI)
    body_T = existe_elimination(body_phi, _T)
    return existe_elimination(body_T, _S)          # temoin_commun_inv_h ⇒ ua=ub


def _transport_ordre():
    """⊢ temoin_commun_h(ua,va,ub,vb) ⇒ (R{ua,ub} ⇔ Rp{va,vb}).  (INCONDITIONNEL —
    compatibilité d'ordre de l'iso commun, transport identique à
    compatibilite_ordre_depuis_temoin.)"""
    Rf, Rpf = _R_de("R"), _R_de("Rp")
    coeur = COH._temoin_commun_coeur("E", "R", "F", "Rp",
                                     _UA, _VA, _UB, _VB, _S, _T, _PHI)
    vu, vv, vup, vvp = var(_UA), var(_VA), var(_UB), var(_VB)
    vphi = var(_PHI)
    fu, fup = E.valeur(vphi, vu), E.valeur(vphi, vup)

    Hc = N.assume(coeur)
    c_iso_etc = conjonction_elim_gauche(Hc)        # …et u∈S et u'∈S et v=φ(u)
    c_vvp = conjonction_elim_droite(Hc)            # v'=φ(u')
    c_iso_uu = conjonction_elim_gauche(c_iso_etc)  # …et u∈S et u'∈S
    c_vv = conjonction_elim_droite(c_iso_etc)      # v=φ(u)
    c_iso_u = conjonction_elim_gauche(c_iso_uu)    # …et u∈S
    c_upS = conjonction_elim_droite(c_iso_uu)      # u'∈S
    c_iso0 = conjonction_elim_gauche(c_iso_u)      # est_segment et est_segment et iso
    c_uS = conjonction_elim_droite(c_iso_u)        # u∈S
    c_iso = conjonction_elim_droite(c_iso0)        # est_isomorphisme_ordre(φ,S,T,R,Rp)
    c_compat = conjonction_elim_droite(c_iso)      # compatible_ordre(φ,S,R,Rp)

    compat_inst = instancie(instancie(c_compat, vu), vup)
    equiv_phi = N.modus_ponens(conjonction_intro(c_uS, c_upS), compat_inst)
    # PONT j→y : compatible_ordre écrit φ(·) en liant « j » ; le reste (v=φ(u)) en « y ».
    fup_j = E.valeur(vphi, vup, b="j")
    equiv_phi = reecrire(equiv_phi, valeur_j_egal_y(vphi, vu),
                         lambda hh: equiv(Rf(vu, vup), Rpf(hh, fup_j)))
    equiv_phi = reecrire(equiv_phi, valeur_j_egal_y(vphi, vup),
                         lambda hh: equiv(Rf(vu, vup), Rpf(fu, hh)))   # Rp{φ(u)[τy],φ(u')[τy]}

    fu_eq_v = N.modus_ponens(c_vv, symetrie(vv, fu))       # φ(u)=v
    fup_eq_vp = N.modus_ponens(c_vvp, symetrie(vvp, fup))  # φ(u')=v'
    eq1 = _leib(fu, vv, fu_eq_v,
                lambda w: equiv(Rf(vu, vup), Rpf(w, fup)), equiv_phi)   # R{u,u'} ⇔ Rp{v,φ(u')}
    eq2 = _leib(fup, vvp, fup_eq_vp,
                lambda w: equiv(Rf(vu, vup), Rpf(vv, w)), eq1)          # R{u,u'} ⇔ Rp{v,v'}

    body_coeur = N.loi_deduction(coeur, eq2)
    body_phi = existe_elimination(body_coeur, _PHI)
    body_T = existe_elimination(body_phi, _T)
    return existe_elimination(body_T, _S)          # temoin_commun_h ⇒ (R{ua,ub}⇔Rp{va,vb})


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 TARGET 1 — compatibilite_inverse_h PROUVÉE.
# ════════════════════════════════════════════════════════════════════════════
def compatibilite_inverse_h_prouve(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ { bo(R,E), bo(R',F) } ⊢ compatibilite_inverse_h.

    🎯🎯 (A) — COHÉRENCE INVERSE de h (= son INJECTIVITÉ par couples) PROUVÉE comme
    THÉORÈME (et NON prise en hypothèse comme dans ensembles_trichotomie_h_iso).

    PREUVE.  Pour (u,v)∈h et (u',v)∈h (MÊME valeur v) :
      • le TÉMOIN COMMUN inverse temoin_commun_inv_h(u,v,u') — UN iso φ:S≅T de segments
        avec u,u'∈S, v=φ(u)=φ(u') — est PROUVÉ (_temoin_inv_prouve) : la FUSION
        (fusion_depuis_coincidence_app, dérivée de la COÏNCIDENCE CLOSE coincidence_univ
        _app) le fournit des deux couples, sous bo(R,E)+bo(R',F)+résidu géométrique ;
      • l'INJECTIVITÉ de l'iso commun (_transport_inverse) donne alors u=u'.
    On recolle la prémisse ((u,v)∈h et (u',v)∈h) ⇒ u=u', puis on UNIVERSALISE.

    ⚠️ NOMS : le corps est bâti aux noms-témoins internes ua,va,ub (imposés par la
    fusion), puis les QUANTIFICATEURS externes sont renommés vers les liants par DÉFAUT
    u,v,u' (corps final = (·,·)∈h avec h opaque ⇒ renommage SANS « @ »).

    theorie=22.  NON vacueux : compatibilite_inverse_h n'est aucune hypothèse (≠ bo,
    ≠ résidu).  Hypothèses HONNÊTES (bons ordres ambiants + résidu géométrique, JAMAIS
    la coïncidence — PROUVÉE — ni la cohérence elle-même)."""
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis (schéma coincidence_univ_app)"
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vup = var(_UA), var(_VA), var(_UB)

    tinv = _temoin_inv_prouve()                    # ⊢ temoin_commun_inv_h(ua,va,ub) [bo,bo,res,couples]
    transport = _transport_inverse()               # temoin_commun_inv_h(ua,va,ub) ⇒ ua=ub
    u_eq_up = N.modus_ponens(tinv, transport)      # ua=ub  [hyps: couples, bo, bo, résidu]

    # recoller la prémisse ((ua,va)∈h et (ub,va)∈h) ⇒ ua=ub
    c1f = appartient(E.couple(vu, vv), h)
    c2f = appartient(E.couple(vup, vv), h)
    prem = et(c1f, c2f)
    Hprem = N.assume(prem)
    res = u_eq_up
    res = N.modus_ponens(conjonction_elim_gauche(Hprem), N.loi_deduction(c1f, res))
    res = N.modus_ponens(conjonction_elim_droite(Hprem), N.loi_deduction(c2f, res))
    body = N.loi_deduction(prem, res)
    full = N.generalisation(_UA, N.generalisation(_VA, N.generalisation(_UB, body)))
    # renommer les 3 quantificateurs externes ua,va,ub → u,v,u' (défauts de la cible)
    return _renommer_quantificateurs(full, [_UA, _VA, _UB], ["u", "v", "up"])


def compatibilite_inverse_h_prouve_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : compatibilite_inverse_h  (la FORMULE (A), défauts)."""
    return H.compatibilite_inverse_h(E_set, R, F_set, Rp)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 TARGET 2 — compatibilite_ordre_h PROUVÉE.
# ════════════════════════════════════════════════════════════════════════════
def compatibilite_ordre_h_prouve(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ { bo(R,E), bo(R',F) } ⊢ compatibilite_ordre_h.

    🎯🎯 (B) — COHÉRENCE D'ORDRE de h (= sa COMPATIBILITÉ D'ORDRE par couples) PROUVÉE
    comme THÉORÈME (et NON prise en hypothèse comme dans ensembles_trichotomie_h_iso).

    PREUVE.  Pour (u,v)∈h et (u',v')∈h :
      • le TÉMOIN COMMUN temoin_commun_h(u,v,u',v') — UN iso φ:S≅T de segments avec
        u,u'∈S, v=φ(u), v'=φ(u') — est PROUVÉ (_temoin_commun_prouve) : la FUSION
        (fusion_depuis_coincidence_app, dérivée de la COÏNCIDENCE CLOSE) le fournit des
        deux couples, sous bo(R,E)+bo(R',F)+résidu géométrique ;
      • la COMPATIBILITÉ D'ORDRE de l'iso commun (_transport_ordre) donne
        R{u,u'} ⇔ Rp{φ(u),φ(u')} = Rp{v,v'}.
    On recolle la prémisse ((u,v)∈h et (u',v')∈h) ⇒ (R{u,u'} ⇔ Rp{v,v'}), puis on
    UNIVERSALISE.

    ⚠️ NOMS : corps aux noms-témoins internes ua,va,ub,vb (fusion), puis quantificateurs
    externes renommés vers les défauts u,v,u',v'.  theorie=22 ; NON vacueux ; hyps
    HONNÊTES (bons ordres ambiants + résidu géométrique)."""
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis (schéma coincidence_univ_app)"
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vup, vvp = var(_UA), var(_VA), var(_UB), var(_VB)

    tch = _temoin_commun_prouve()                  # ⊢ temoin_commun_h(ua,va,ub,vb) [bo,bo,res,couples]
    transport = _transport_ordre()                 # temoin_commun_h ⇒ (R{ua,ub}⇔Rp{va,vb})
    equiv_uu = N.modus_ponens(tch, transport)      # R{ua,ub} ⇔ Rp{va,vb}  [hyps: couples, bo,bo,résidu]

    c1f = appartient(E.couple(vu, vv), h)
    c2f = appartient(E.couple(vup, vvp), h)
    prem = et(c1f, c2f)
    Hprem = N.assume(prem)
    res = equiv_uu
    res = N.modus_ponens(conjonction_elim_gauche(Hprem), N.loi_deduction(c1f, res))
    res = N.modus_ponens(conjonction_elim_droite(Hprem), N.loi_deduction(c2f, res))
    body = N.loi_deduction(prem, res)
    full = N.generalisation(_UA, N.generalisation(_VA,
        N.generalisation(_UB, N.generalisation(_VB, body))))
    return _renommer_quantificateurs(full, [_UA, _VA, _UB, _VB], ["u", "v", "up", "vp"])


def compatibilite_ordre_h_prouve_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : compatibilite_ordre_h  (la FORMULE (B), défauts)."""
    return H.compatibilite_ordre_h(E_set, R, F_set, Rp)


def h_bien_defini_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 2 HYPOTHÈSES SURVIVANTES (documentation / test miroir) communes aux deux
    cohérences PROUVÉES :  [ bo(R,E), bo(R',F) ].  ⚠️ `residu_univ_app` ÉLIMINÉ.

    Identiques aux hypothèses de fusion_depuis_coincidence_app (la FUSION dérivée de
    la coïncidence CLOSE, résidu DÉRIVÉ de residu_univ_app_renforce)."""
    return FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp)


__all__ = [
    "compatibilite_inverse_h_prouve", "compatibilite_inverse_h_prouve_cible",
    "compatibilite_ordre_h_prouve", "compatibilite_ordre_h_prouve_cible",
    "h_bien_defini_hypotheses",
]
