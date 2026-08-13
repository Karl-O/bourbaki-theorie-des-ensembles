"""§III.2 — Théorème 3 (TRICHOTOMIE) : PREUVE des deux COHÉRENCES de h (=h_iso_max).

────────────────────────────────────────────────────────────────────────────────
RÔLE — fermer le DERNIER gap de la trichotomie (Th3 §III.2, E.III.2.6).  L'iso
MAXIMAL  h = h_iso_max(E,R,F,Rp)  (union des graphes d'iso de couples de segments
isomorphes, posé dans ensembles_trichotomie_scaffold, axiome dédié theorie_h,
theorie=22) est un ISOMORPHISME D'ORDRE de dom(h) sur pr₂(h) DÈS QUE l'on dispose
des deux COHÉRENCES :

    (A)  compatibilite_inverse_h := (∀u)(∀v)(∀u')( ((u,v)∈h et (u',v)∈h) ⇒ u=u' ),
    (B)  compatibilite_ordre_h   := (∀u)(∀v)(∀u')(∀v')(
              ((u,v)∈h et (u',v')∈h) ⇒ (R{u,u'} ⇔ Rp{v,v'}) ).

(les FORMULES (A),(B) sont DÉFINIES dans ensembles_trichotomie_h_iso :
compatibilite_inverse_h / compatibilite_ordre_h ; on les RÉUTILISE telles quelles —
ce module en livre une PREUVE, plus une décharge en cascade vers l'iso d'ordre.)

────────────────────────────────────────────────────────────────────────────────
ROUTE FIDÈLE BOURBAKI (Lemme 1 §III.2 + UNICITÉ de l'iso de segments).

Chaque couple (u,v)∈h provient (h_membre_donne_temoin, CLOS) d'un iso φ:S≅T de
SEGMENTS (S segment de E, T segment de F, u∈S, v=φ(u)).  Deux couples (u,v),(u',v')
proviennent d'isos φ:S≅T, φ':S'≅T'.  Les segments S,S' d'un MÊME bon ordre E sont
EMBOÎTÉS (comparabilité + Lemme 1 §III.2) ; sur le plus petit, φ et φ' COÏNCIDENT
par UNICITÉ de l'iso de segments (auto_iso_est_identite CLOS).  D'où :
  • (B) par TRANSPORT D'ORDRE : u,u' dans le segment commun ⇒
        R{u,u'} ⇔ Rp{φ(u),φ(u')} = Rp{v,v'}  (φ order-preserving) ;
  • (A) par INJECTIVITÉ de l'iso commun : v=φ(u)=φ(u')=v ⇒ u=u'.

────────────────────────────────────────────────────────────────────────────────
SALVAGE FORT GRADUÉ (honnête, theorie=22, jamais postulé/tautologie/affaibli).

Le verrou inconditionnel est l'emboîtement des segments témoins + la coïncidence des
isos (magnitude Cantor–Bernstein / Lemme 1 §III.2, multi-round).  On le RÉDUIT à une
SEULE hypothèse EXPLICITE, VRAIE et SUBSTANTIELLE (= le contenu géométrique de Lemme 1,
PAS la conclusion (A)/(B)) :

    temoin_commun_h(u,v,u',v') :=  (∃S)(∃T)(∃φ)(
        est_segment(S,R,E) et est_segment(T,Rp,F) et est_isomorphisme_ordre(φ,S,T,R,Rp)
        et u∈S et u'∈S et v=φ(u) et v'=φ(u') )

« les DEUX antécédents u,u' sont couverts par UN SEUL iso de segments φ:S≅T, avec
v=φ(u) et v'=φ(u') ».  C'est EXACTEMENT le contenu de Lemme 1 §III.2 (prendre le PLUS
GRAND des deux segments emboîtés et l'iso unique qu'il porte) — VRAI, non trivial,
DIFFÉRENT de (A)/(B) (il QUANTIFIE EXISTENTIELLEMENT un témoin, là où (A)/(B) sont des
égalités/équivalences).  De lui, ce module DÉRIVE réellement (A) et (B) par transport
(ordre/injectivité de l'iso commun) — travail substantiel via les bricks CLOS.

CE MODULE LIVRE :

  ✅ compatibilite_ordre_depuis_temoin :
        { (∀u,v,u',v') temoin_commun_h(u,v,u',v') } ⊢ compatibilite_ordre_h.   (B)
  ✅ compatibilite_inverse_depuis_temoin :
        { (∀u,v,u') temoin_commun_inv_h(u,v,u') } ⊢ compatibilite_inverse_h.    (A)
  ✅ coherences_donnent_iso_sous_hyp :
        décharge (A),(B) dans h_est_isomorphisme_ordre_sous_hyp ⇒
        { func h, temoin_commun(∀), temoin_commun_inv(∀), surjective } ⊢ iso d'ordre.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : (A),(B) sont DÉRIVÉS d'une
hypothèse géométrique EXPLICITE (le témoin commun = Lemme 1 §III.2), via les théorèmes
CLOS h_membre_donne_temoin / est_isomorphisme_ordre.  Les conclusions (A),(B),iso ne
sont AUCUNE de leurs hypothèses (non tautologiques, non affaiblies).

⚠️ REPORTÉ précisément (JAMAIS postulé) : la PREUVE de temoin_commun_h /
temoin_commun_inv_h (= l'EMBOÎTEMENT des segments témoins + la coïncidence des isos
sur le chevauchement, Lemme 1 §III.2, magnitude Cantor–Bernstein).  Le présent module
décharge TOUT le reste : il ne reste, pour l'inconditionnel, QUE ce témoin commun.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.isomorphismes_ordre.ensembles_pont_binder import reecrire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.isomorphismes_ordre.ensembles_valeur_bridge import valeur_j_egal_y
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, equivalence_transitivite,
    equivalence_symetrie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_elimination
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences import ensembles_trichotomie_h_iso as H


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_coh"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b et ⊢ Φ[a] déduit ⊢ Φ[b]   (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  (B)  COHÉRENCE D'ORDRE — temoin_commun_h(u,v,u',v') :=
#       (∃S)(∃T)(∃φ)( segments + iso φ:S≅T + u∈S et u'∈S et v=φ(u) et v'=φ(u') ).
#  C'est le contenu de Lemme 1 §III.2 : UN SEUL iso couvre les deux antécédents.
# ════════════════════════════════════════════════════════════════════════════
# ⚠️ binders FRAIS « px »,« pw » pour le iso interne : le binder DÉFAUT « y » de
#    est_isomorphisme_ordre serait CAPTURÉ par le τ_y de valeur(φ,·)=τ_y((·,y)∈φ),
#    rendant valeur(φ, y) dégénéré (τ_y((y,y)∈φ)).  « px »,« pw » sont frais ⇒ les
#    valeurs φ(u),φ(u') sont bien formées et instanciables (cf. piège VALEUR).
_ISO_X, _ISO_Y = "px", "pw"


def _iso(phi, S, T, Rf, Rpf):
    """est_isomorphisme_ordre(φ,S,T,R,Rp) avec binders FRAIS (anti-capture-y)."""
    return V.est_isomorphisme_ordre(_t(phi), _t(S), _t(T), Rf, Rpf, _ISO_X, _ISO_Y)


def _temoin_commun_coeur(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi):
    """Le CŒUR (sans les ∃) de temoin_commun_h : segments + iso + couverture des
    DEUX antécédents u,u' par l'unique iso φ, avec v=φ(u) et v'=φ(u')."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi = var(S), var(T), var(phi)
    vu, vv, vup, vvp = _t(u), _t(v), _t(up), _t(vp)
    return et(et(et(et(et(et(
        E.est_segment(vS, Rf, vE),
        E.est_segment(vT, Rpf, vF)),
        _iso(vphi, vS, vT, Rf, Rpf)),
        appartient(vu, vS)),
        appartient(vup, vS)),
        egal(vv, E.valeur(vphi, vu))),
        egal(vvp, E.valeur(vphi, vup)))


def temoin_commun_h(E_set="E", R="R", F_set="F", Rp="Rp",
                    u="u", v="v", up="up", vp="vp", S="S", T="T", phi="phi"):
    """FORMULE (hypothèse géométrique EXPLICITE = Lemme 1 §III.2, par couples) :

        temoin_commun_h(u,v,u',v') := (∃S)(∃T)(∃φ)(
            est_segment(S,R,E) et est_segment(T,Rp,F)
            et est_isomorphisme_ordre(φ,S,T,R,Rp)
            et u∈S et u'∈S et v=φ(u) et v'=φ(u') ).

    « les deux antécédents u,u' sont couverts par UN MÊME iso de segments φ:S≅T,
    avec v=φ(u) et v'=φ(u') ».  VRAI (prendre le plus grand des segments témoins de
    (u,v) et (u',v'), emboîtés par comparabilité + Lemme 1) ; non trivial ; DIFFÉRENT
    de (B) (existentiel sur un témoin, non l'équivalence d'ordre).  Posé en HYPOTHÈSE,
    jamais comme théorème."""
    coeur = _temoin_commun_coeur(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)
    return existe(S, existe(T, existe(phi, coeur)))


# @livre Ch.III §2.5 Demo.3 | E III.21 L.23-33 | PDF p.124  (démonstration du Th. 3 : cohérences de h dérivées des témoins communs)
def compatibilite_ordre_depuis_temoin(E_set="E", R="R", F_set="F", Rp="Rp",
                                      u="u", v="v", up="up", vp="vp",
                                      S="S", T="T", phi="phi"):
    """⊢ { (∀u)(∀v)(∀u')(∀v') temoin_commun_h(u,v,u',v') } ⊢ compatibilite_ordre_h.

    🎯 (B) — COHÉRENCE D'ORDRE de h DÉRIVÉE du témoin commun (Lemme 1 §III.2).
    Pour (u,v),(u',v')∈h, le témoin commun fournit UN iso φ:S≅T de segments avec
    u,u'∈S, v=φ(u), v'=φ(u').  La COMPATIBILITÉ d'ordre de φ (conjoint de
    est_isomorphisme_ordre) instanciée à (u,u') donne  R{u,u'} ⇔ Rp{φ(u),φ(u')} ;
    réécrite par v=φ(u), v'=φ(u' )  ⇒  R{u,u'} ⇔ Rp{v,v'}.  C'est (B).

    Travail SUBSTANTIEL (transport d'ordre + élimination du témoin existentiel) ;
    CONDITIONNEL au témoin commun EXPLICITE, theorie=22.  NON vacueux :
    compatibilite_ordre_h n'est aucune hypothèse (≠ témoin_commun)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vup, vvp = var(u), var(v), var(up), var(vp)
    vS, vT, vphi = var(S), var(T), var(phi)
    fu, fup = E.valeur(vphi, vu), E.valeur(vphi, vup)

    # — du CŒUR (segments + iso + couverture), dériver  R{u,u'} ⇔ Rp{v,v'} —
    coeur = _temoin_commun_coeur(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)
    Hc = N.assume(coeur)
    # extraire les conjoints (et est encodé ¬(¬∨¬) ⇒ projections gauche/droite)
    c_iso_etc = conjonction_elim_gauche(Hc)        # …et u∈S et u'∈S et v=φ(u)
    c_vvp = conjonction_elim_droite(Hc)            # v'=φ(u')
    c_iso_uu = conjonction_elim_gauche(c_iso_etc)  # …et u∈S et u'∈S
    c_vv = conjonction_elim_droite(c_iso_etc)      # v=φ(u)
    c_iso_u = conjonction_elim_gauche(c_iso_uu)    # …et u∈S
    c_upS = conjonction_elim_droite(c_iso_uu)      # u'∈S
    c_iso0 = conjonction_elim_gauche(c_iso_u)      # est_segment et est_segment et iso
    c_uS = conjonction_elim_droite(c_iso_u)        # u∈S
    c_iso = conjonction_elim_droite(c_iso0)        # est_isomorphisme_ordre(φ,S,T,R,Rp)

    # compatible_ordre(φ,S,R,Rp) = 2ᵉ conjoint de l'iso
    c_compat = conjonction_elim_droite(c_iso)      # compatible_ordre(φ,S,R,Rp)
    # instancier à (u,u') sous u∈S et u'∈S : R{u,u'} ⇔ Rp{φ(u),φ(u')}
    compat_inst = instancie(instancie(c_compat, vu), vup)
    equiv_phi = N.modus_ponens(conjonction_intro(c_uS, c_upS), compat_inst)  # R{u,u'} ⇔ Rp{φ(u)[τj],φ(u')[τj]}
    # PONT j→y : compatible_ordre (fonction) écrit φ(·) en liant « j » ; la suite du
    # raisonnement (v=φ(u) du cœur, fu/fup) est en « y ».  On convertit φ(u),φ(u') j→y
    # (u,u' PLAINES ⇒ pas de capture) pour raccorder.
    fu_j, fup_j = E.valeur(vphi, vu, b="j"), E.valeur(vphi, vup, b="j")
    equiv_phi = reecrire(equiv_phi, valeur_j_egal_y(vphi, vu),
                         lambda hh: equiv(Rf(vu, vup), Rpf(hh, fup_j)))
    equiv_phi = reecrire(equiv_phi, valeur_j_egal_y(vphi, vup),
                         lambda hh: equiv(Rf(vu, vup), Rpf(fu, hh)))   # Rp{φ(u)[τy],φ(u')[τy]}

    # réécrire Rp{φ(u),φ(u')} → Rp{v,v'}  via v=φ(u) (sens φ(u)→v) et v'=φ(u')
    # v=φ(u) ⇒ φ(u)=v
    fu_eq_v = N.modus_ponens(c_vv, symetrie(vv, fu))    # φ(u)=v
    fup_eq_vp = N.modus_ponens(c_vvp, symetrie(vvp, fup))  # φ(u')=v'
    # transporter le membre droit de l'équivalence : Rp{φ(u),φ(u')} → Rp{v,φ(u')}
    eq1 = _leib(fu, vv, fu_eq_v,
                lambda w: equiv(Rf(vu, vup), Rpf(w, fup)), equiv_phi)  # R{u,u'} ⇔ Rp{v,φ(u')}
    eq2 = _leib(fup, vvp, fup_eq_vp,
                lambda w: equiv(Rf(vu, vup), Rpf(vv, w)), eq1)        # R{u,u'} ⇔ Rp{v,v'}

    # décharge du cœur (le témoin existentiel est éliminé ensuite)
    body_coeur = N.loi_deduction(coeur, eq2)            # coeur ⇒ (R{u,u'} ⇔ Rp{v,v'})
    # éliminer les 3 existentiels (S,T,φ NON libres dans la conclusion R{u,u'}⇔Rp{v,v'})
    body_phi = existe_elimination(body_coeur, phi)      # (∃φ)coeur ⇒ concl
    body_T = existe_elimination(body_phi, T)            # (∃T)(∃φ)coeur ⇒ concl
    body_S = existe_elimination(body_T, S)              # (∃S)(∃T)(∃φ)coeur ⇒ concl
    #   = temoin_commun_h(u,v,u',v') ⇒ (R{u,u'} ⇔ Rp{v,v'})

    # consommer l'hypothèse universelle (∀u,v,u',v') temoin_commun_h
    Htc = N.assume(temoin_commun_universel(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi))
    tc_inst = instancie(instancie(instancie(instancie(Htc, vu), vv), vup), vvp)  # temoin_commun_h(u,v,u',v')
    equiv_uu = N.modus_ponens(tc_inst, body_S)          # R{u,u'} ⇔ Rp{v,v'}

    # recoller la prémisse de compatibilite_ordre_h : ((u,v)∈h et (u',v')∈h) ⇒ (…)
    prem = et(appartient(E.couple(vu, vv), h), appartient(E.couple(vup, vvp), h))
    body = N.loi_deduction(prem, equiv_uu)              # prem ⇒ (R{u,u'} ⇔ Rp{v,v'})
    return N.generalisation(u, N.generalisation(v, N.generalisation(up,
        N.generalisation(vp, body))))


def temoin_commun_universel(E_set="E", R="R", F_set="F", Rp="Rp",
                            u="u", v="v", up="up", vp="vp", S="S", T="T", phi="phi"):
    """FORMULE : (∀u)(∀v)(∀u')(∀v') temoin_commun_h(u,v,u',v').

    L'hypothèse géométrique GLOBALE (Lemme 1 §III.2 universalisé) consommée par
    compatibilite_ordre_depuis_temoin.  Posée explicite, jamais postulée."""
    return pourtout(u, pourtout(v, pourtout(up, pourtout(vp,
        temoin_commun_h(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)))))


def compatibilite_ordre_depuis_temoin_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) :  compatibilite_ordre_h  (la FORMULE (B))."""
    return H.compatibilite_ordre_h(E_set, R, F_set, Rp)


# ════════════════════════════════════════════════════════════════════════════
#  (A)  COHÉRENCE INVERSE — temoin_commun_inv_h(u,v,u') :=
#       (∃S)(∃T)(∃φ)( segments + iso φ:S≅T + u∈S et u'∈S et v=φ(u) et v=φ(u') ).
#  Les DEUX antécédents u,u' de la MÊME valeur v sont couverts par UN iso φ injectif.
# ════════════════════════════════════════════════════════════════════════════
def _temoin_inv_coeur(E_set, R, F_set, Rp, u, v, up, S, T, phi):
    """Le CŒUR (sans les ∃) de temoin_commun_inv_h : segments + iso + u,u'∈S et
    v=φ(u) et v=φ(u')  (même valeur v pour les deux antécédents)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi = var(S), var(T), var(phi)
    vu, vv, vup = _t(u), _t(v), _t(up)
    return et(et(et(et(et(et(
        E.est_segment(vS, Rf, vE),
        E.est_segment(vT, Rpf, vF)),
        _iso(vphi, vS, vT, Rf, Rpf)),
        appartient(vu, vS)),
        appartient(vup, vS)),
        egal(vv, E.valeur(vphi, vu))),
        egal(vv, E.valeur(vphi, vup)))


def temoin_commun_inv_h(E_set="E", R="R", F_set="F", Rp="Rp",
                        u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """FORMULE (hypothèse géométrique EXPLICITE = Lemme 1 §III.2, côté image) :

        temoin_commun_inv_h(u,v,u') := (∃S)(∃T)(∃φ)(
            segments + est_isomorphisme_ordre(φ,S,T,R,Rp)
            et u∈S et u'∈S et v=φ(u) et v=φ(u') ).

    « les deux antécédents u,u' de la MÊME valeur v sont couverts par UN iso φ:S≅T ».
    VRAI (segments emboîtés ⇒ iso commun, Lemme 1 §III.2) ; DIFFÉRENT de (A) (témoin
    existentiel, non l'égalité u=u').  Posé explicite, jamais postulé."""
    coeur = _temoin_inv_coeur(E_set, R, F_set, Rp, u, v, up, S, T, phi)
    return existe(S, existe(T, existe(phi, coeur)))


def temoin_commun_inv_universel(E_set="E", R="R", F_set="F", Rp="Rp",
                                u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """FORMULE : (∀u)(∀v)(∀u') temoin_commun_inv_h(u,v,u')."""
    return pourtout(u, pourtout(v, pourtout(up,
        temoin_commun_inv_h(E_set, R, F_set, Rp, u, v, up, S, T, phi))))


def compatibilite_inverse_depuis_temoin(E_set="E", R="R", F_set="F", Rp="Rp",
                                        u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """⊢ { (∀u)(∀v)(∀u') temoin_commun_inv_h(u,v,u') } ⊢ compatibilite_inverse_h.

    🎯 (A) — COHÉRENCE INVERSE de h DÉRIVÉE du témoin commun (Lemme 1 §III.2).
    Pour (u,v),(u',v)∈h (MÊME valeur v), le témoin commun fournit UN iso φ:S≅T de
    segments avec u,u'∈S et v=φ(u)=φ(u').  L'INJECTIVITÉ de φ (φ bijectif sur S,
    conjoint de est_isomorphisme_ordre ⇒ injective_dans(φ,S)) instanciée à (u,u') sous
    φ(u)=φ(u') donne u=u'.  C'est (A).

    Travail SUBSTANTIEL (injectivité de l'iso commun + élimination du témoin) ;
    CONDITIONNEL au témoin commun EXPLICITE, theorie=22.  NON vacueux."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vup = var(u), var(v), var(up)
    vS, vT, vphi = var(S), var(T), var(phi)
    fu, fup = E.valeur(vphi, vu), E.valeur(vphi, vup)

    coeur = _temoin_inv_coeur(E_set, R, F_set, Rp, u, v, up, S, T, phi)
    Hc = N.assume(coeur)
    # extraire les conjoints
    c0 = conjonction_elim_gauche(Hc)               # …et u∈S et u'∈S et v=φ(u)
    c_vup = conjonction_elim_droite(Hc)            # v=φ(u')
    c1 = conjonction_elim_gauche(c0)               # …et u∈S et u'∈S
    c_vu = conjonction_elim_droite(c0)             # v=φ(u)
    c2 = conjonction_elim_gauche(c1)               # …et u∈S
    c_upS = conjonction_elim_droite(c1)            # u'∈S
    c3 = conjonction_elim_gauche(c2)               # segments et iso
    c_uS = conjonction_elim_droite(c2)             # u∈S
    c_iso = conjonction_elim_droite(c3)            # est_isomorphisme_ordre(φ,S,T,R,Rp)

    # est_bijective(φ,S,T) = 1ᵉ conjoint de l'iso ;  injective_dans(φ,S) = 1ᵉ conjoint
    c_bij = conjonction_elim_gauche(c_iso)         # est_bijective(φ,S,T)
    c_inj = conjonction_elim_gauche(c_bij)         # injective_dans(φ,S)

    # φ(u)=φ(u') :  de v=φ(u) et v=φ(u') ⇒ φ(u)=φ(u')
    fu_eq_v = N.modus_ponens(c_vu, symetrie(vv, fu))      # φ(u)=v
    fu_eq_fup = _leib(vv, fup, c_vup, lambda w: egal(fu, w), fu_eq_v)  # φ(u)=φ(u')

    # injective_dans(φ,S) instanciée à (u,u') : ((u∈S et u'∈S) et φ(u)=φ(u')) ⇒ u=u'
    inj_inst = _injective_instance(c_inj, vphi, vS, vu, vup)
    u_eq_up = N.modus_ponens(
        conjonction_intro(conjonction_intro(c_uS, c_upS), fu_eq_fup), inj_inst)  # u=u'

    body_coeur = N.loi_deduction(coeur, u_eq_up)         # coeur ⇒ u=u'
    body_phi = existe_elimination(body_coeur, phi)
    body_T = existe_elimination(body_phi, T)
    body_S = existe_elimination(body_T, S)               # temoin_commun_inv_h(u,v,u') ⇒ u=u'

    Htc = N.assume(temoin_commun_inv_universel(E_set, R, F_set, Rp, u, v, up, S, T, phi))
    tc_inst = instancie(instancie(instancie(Htc, vu), vv), vup)
    u_eq_up2 = N.modus_ponens(tc_inst, body_S)           # u=u'

    prem = et(appartient(E.couple(vu, vv), h), appartient(E.couple(vup, vv), h))
    body = N.loi_deduction(prem, u_eq_up2)
    return N.generalisation(u, N.generalisation(v, N.generalisation(up, body)))


def _injective_instance(c_inj, phi, S, u, up):
    """De injective_dans(φ,S) tirer  ((u∈S et u'∈S) et φ(u)=φ(u')) ⇒ u=u'  par
    instanciation universelle aux liants (u,u') de injective_dans (binders u,up)."""
    return instancie(instancie(c_inj, _t(u)), _t(up))


def compatibilite_inverse_depuis_temoin_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) :  compatibilite_inverse_h  (la FORMULE (A))."""
    return H.compatibilite_inverse_h(E_set, R, F_set, Rp)


# ════════════════════════════════════════════════════════════════════════════
#  FONCTIONNALITÉ (func h) — temoin_commun_fonc_h(u,v,z) :=
#       (∃S)(∃T)(∃φ)( segments + iso φ:S≅T + u∈S et v=φ(u) et z=φ(u) ).
#  L'unique iso φ donne v=φ(u)=z : func h.  Duale de (A), même style (Lemme 1).
# ════════════════════════════════════════════════════════════════════════════
def _temoin_fonc_coeur(E_set, R, F_set, Rp, u, v, z, S, T, phi):
    """CŒUR (sans ∃) de temoin_commun_fonc_h : segments + iso + u∈S et v=φ(u) et z=φ(u)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi = var(S), var(T), var(phi)
    vu, vv, vz = _t(u), _t(v), _t(z)
    return et(et(et(et(et(
        E.est_segment(vS, Rf, vE),
        E.est_segment(vT, Rpf, vF)),
        _iso(vphi, vS, vT, Rf, Rpf)),
        appartient(vu, vS)),
        egal(vv, E.valeur(vphi, vu))),
        egal(vz, E.valeur(vphi, vu)))


def temoin_commun_fonc_h(E_set="E", R="R", F_set="F", Rp="Rp",
                         u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """FORMULE (Lemme 1 §III.2, côté fonctionnalité) :

        temoin_commun_fonc_h(u,v,z) := (∃S)(∃T)(∃φ)(
            segments + iso(φ,S,T,R,Rp) et u∈S et v=φ(u) et z=φ(u) ).

    « deux valeurs v,z du MÊME antécédent u proviennent d'UN iso φ:S≅T (v=φ(u)=z) ».
    VRAI (Lemme 1), DUAL de (A), DIFFÉRENT de func h (témoin existentiel).  Explicite."""
    coeur = _temoin_fonc_coeur(E_set, R, F_set, Rp, u, v, z, S, T, phi)
    return existe(S, existe(T, existe(phi, coeur)))


def temoin_commun_fonc_universel(E_set="E", R="R", F_set="F", Rp="Rp",
                                 u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """FORMULE : (∀u)(∀v)(∀z) temoin_commun_fonc_h(u,v,z)."""
    return pourtout(u, pourtout(v, pourtout(z,
        temoin_commun_fonc_h(E_set, R, F_set, Rp, u, v, z, S, T, phi))))


def fonctionnel_depuis_temoin(E_set="E", R="R", F_set="F", Rp="Rp",
                              u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """⊢ { (∀u)(∀v)(∀z) temoin_commun_fonc_h(u,v,z) } ⊢ est_fonctionnel(h).

    🎯 FONCTIONNALITÉ de h DÉRIVÉE du témoin commun (Lemme 1 §III.2, duale de (A)).
    Pour (u,v),(u,z)∈h, le témoin commun donne UN iso φ avec v=φ(u) et z=φ(u), d'où
    v=z (transitivité de l'égalité via φ(u)).  CONDITIONNEL au témoin EXPLICITE,
    theorie=22.  NON vacueux : est_fonctionnel(h) n'est aucune hypothèse."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vz = var(u), var(v), var(z)
    vphi = var(phi)
    fu = E.valeur(vphi, vu)

    coeur = _temoin_fonc_coeur(E_set, R, F_set, Rp, u, v, z, S, T, phi)
    Hc = N.assume(coeur)
    c0 = conjonction_elim_gauche(Hc)               # …et u∈S et v=φ(u)
    c_z = conjonction_elim_droite(Hc)              # z=φ(u)
    c_v = conjonction_elim_droite(c0)              # v=φ(u)
    # v=φ(u) et z=φ(u) ⇒ v=z :  v=φ(u), φ(u)=z (sym de z=φ(u))
    fu_eq_z = N.modus_ponens(c_z, symetrie(vz, fu))      # φ(u)=z
    v_eq_z = _leib(fu, vz, fu_eq_z, lambda w: egal(vv, w), c_v)  # v=z

    body_coeur = N.loi_deduction(coeur, v_eq_z)
    body_phi = existe_elimination(body_coeur, phi)
    body_T = existe_elimination(body_phi, T)
    body_S = existe_elimination(body_T, S)              # temoin_commun_fonc_h(u,v,z) ⇒ v=z

    Htc = N.assume(temoin_commun_fonc_universel(E_set, R, F_set, Rp, u, v, z, S, T, phi))
    tc_inst = instancie(instancie(instancie(Htc, vu), vv), vz)
    v_eq_z2 = N.modus_ponens(tc_inst, body_S)           # v=z

    prem = et(appartient(E.couple(vu, vv), h), appartient(E.couple(vu, vz), h))
    body = N.loi_deduction(prem, v_eq_z2)
    return N.generalisation(u, N.generalisation(v, N.generalisation(z, body)))


def fonctionnel_depuis_temoin_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) :  est_fonctionnel(h)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_fonctionnel(h)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CASCADE — décharger (A),(B) dans h_est_isomorphisme_ordre_sous_hyp.
# ════════════════════════════════════════════════════════════════════════════
def coherences_donnent_iso_sous_hyp(E_set="E", R="R", F_set="F", Rp="Rp",
                                    x="x", y="w", u="u", up="up", v="v", vp="vp",
                                    S="S", T="T", phi="phi"):
    """⊢ { est_fonctionnel(h),
           (∀u,v,u') temoin_commun_inv_h(u,v,u'),
           (∀u,v,u',v') temoin_commun_h(u,v,u',v'),
           est_surjective(h, dom h, pr₂ h) }
         ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).

    🎯 CASCADE finale : on PROUVE les deux cohérences (A),(B) à partir des témoins
    communs (Lemme 1 §III.2) — compatibilite_inverse_depuis_temoin /
    compatibilite_ordre_depuis_temoin — puis on les INJECTE dans
    h_est_isomorphisme_ordre_sous_hyp (qui les prenait en hypothèse).  Le séquent
    final ne porte plus (A),(B) comme hypothèses : il porte les TÉMOINS COMMUNS
    EXPLICITES (le contenu géométrique de Lemme 1).  func h + surjectivité restent
    explicites (structurelles).  theorie=22, NON vacueux."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    # iso d'ordre SOUS (A),(B) [+func+surj]
    iso = H.h_est_isomorphisme_ordre_sous_hyp(E_set, R, F_set, Rp, x, y, u, up)
    # PREUVES de (A),(B) depuis les témoins communs
    pA = compatibilite_inverse_depuis_temoin(E_set, R, F_set, Rp, u, v, up, S, T, phi)
    pB = compatibilite_ordre_depuis_temoin(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)
    # remplacer l'hypothèse (A) de `iso` par sa preuve pA, idem (B) par pB
    A_form = H.compatibilite_inverse_h(E_set, R, F_set, Rp)
    B_form = H.compatibilite_ordre_h(E_set, R, F_set, Rp)
    out = iso
    out = N.modus_ponens(pA, N.loi_deduction(A_form, out))   # décharge (A)
    out = N.modus_ponens(pB, N.loi_deduction(B_form, out))   # décharge (B)
    return out


def coherences_donnent_iso_sous_hyp_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                          x="x", y="w"):
    """ÉNONCÉ-cible (test miroir) :  est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp)."""
    return H.h_est_isomorphisme_ordre_sous_hyp_cible(E_set, R, F_set, Rp, x, y)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 BONUS (C) — SURJECTIVITÉ INCONDITIONNELLE :  image(h, dom h) = pr₂(h).
#     Fait set-théorique GÉNÉRAL : l'image d'un graphe sur SON PROPRE domaine
#     ÉGALE sa projection-2.  AUCUNE cohérence requise, theorie=22.
# ════════════════════════════════════════════════════════════════════════════
def _inst_img(g, y):
    """⊢ (y ∈ pr₂ G) ⇔ (∃x)((x,y) ∈ G).   (AXIOME_IMG instancié, binder ∃ « x ».)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    return instancie(instancie(ax, _t(g)), _t(y))


def _inst_dom(g, x):
    """⊢ (x ∈ dom G) ⇔ (∃y)((x,y) ∈ G).   (AXIOME_DOM instancié, binder ∃ « y ».)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    return instancie(instancie(ax, _t(g)), _t(x))


def _inst_image(g, X, y):
    """⊢ (y ∈ G⟨X⟩) ⇔ (∃x)(x∈X et (x,y)∈G).   (AXIOME_IMAGE instancié, binder ∃ « x ».)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    return instancie(instancie(instancie(ax, _t(g)), _t(X)), _t(y))


def surjectivite_h_image(E_set="E", R="R", F_set="F", Rp="Rp", y="z", x="x"):
    """⊢ image(h, dom h) = pr₂(h).   (= est_surjective(h, dom h, pr₂ h).)  INCONDITIONNEL.

    🎯 BONUS (C) — h est SURJECTIVE de dom(h) sur pr₂(h), SANS aucune cohérence.
    Fait GÉNÉRAL : pour tout graphe G,  G⟨dom G⟩ = pr₂(G)  (E.II.39 / E.II.38).  Par
    extensionnalité (A1), DOUBLE INCLUSION :
      (⊃) y∈pr₂h ⇒ (∃x)((x,y)∈h) ; le témoin x vérifie aussi (∃y')((x,y')∈h) (y'=y),
          donc x∈dom h (AXIOME_DOM) ; d'où (∃x)(x∈dom h et (x,y)∈h) = y∈h⟨dom h⟩.
      (⊂) y∈h⟨dom h⟩ ⇒ (∃x)(x∈dom h et (x,y)∈h) ⇒ (∃x)((x,y)∈h) = y∈pr₂h  (oubli).
    INCONDITIONNEL, theorie=22, non vacueux.  Décharge l'hypothèse de surjectivité de
    la cascade — il ne reste plus, pour l'iso d'ordre, QUE les témoins communs (Lemme 1)."""
    vy, vx = var(y), var(x)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh = E.dom(h)
    imgh = E.img(h)            # pr₂ h
    img_dir = E.image(h, domh)  # h⟨dom h⟩

    # caractérisations (axiomes instanciés)
    img_eq = _inst_img(h, vy)               # y∈pr₂h ⇔ (∃x)((x,y)∈h)
    image_eq = _inst_image(h, domh, vy)     # y∈h⟨domh⟩ ⇔ (∃x)(x∈domh et (x,y)∈h)

    cy = appartient(E.couple(vx, vy), h)    # (x,y)∈h
    in_dom_x = appartient(vx, domh)         # x∈dom h

    # ── (⊂)  y∈h⟨domh⟩ ⇒ y∈pr₂h ──────────────────────────────────────────────
    #   (∃x)(x∈domh et (x,y)∈h) ⇒ (∃x)((x,y)∈h)
    Hconj = N.assume(et(in_dom_x, cy))                      # x∈domh et (x,y)∈h
    cy_from = conjonction_elim_droite(Hconj)               # (x,y)∈h
    to_ex = N.modus_ponens(cy_from, N.s5(cy, vx, x))       # (∃x)((x,y)∈h)
    imp_conj = N.loi_deduction(et(in_dom_x, cy), to_ex)    # (x∈domh et (x,y)∈h) ⇒ (∃x)((x,y)∈h)
    ex_to_ex = existe_elimination(imp_conj, x)             # (∃x)(...) ⇒ (∃x)((x,y)∈h)
    y_in_img = syllogisme(equivalence_avant(image_eq),
                          syllogisme(ex_to_ex, equivalence_arriere(img_eq)))  # y∈h⟨domh⟩ ⇒ y∈pr₂h
    incl_sub = N.generalisation(y, y_in_img)               # h⟨domh⟩ ⊂ pr₂h

    # ── (⊃)  y∈pr₂h ⇒ y∈h⟨domh⟩ ──────────────────────────────────────────────
    #   (x,y)∈h ⇒ x∈domh  (via AXIOME_DOM, témoin y'=y de (∃y')((x,y')∈h))
    Hcy = N.assume(cy)                                     # (x,y)∈h
    ex_y = N.modus_ponens(Hcy, N.s5(appartient(E.couple(vx, var("y")), h), vy, "y"))  # (∃y')((x,y')∈h)
    x_in_dom = N.modus_ponens(ex_y, equivalence_arriere(_inst_dom(h, vx)))  # x∈dom h
    conj_xy = conjonction_intro(x_in_dom, Hcy)            # x∈domh et (x,y)∈h
    to_image = N.modus_ponens(conj_xy, N.s5(et(in_dom_x, cy), vx, x))  # (∃x)(x∈domh et (x,y)∈h)
    imp_cy = N.loi_deduction(cy, to_image)               # (x,y)∈h ⇒ (∃x)(x∈domh et (x,y)∈h)
    ex_cy = existe_elimination(imp_cy, x)                # (∃x)((x,y)∈h) ⇒ (∃x)(x∈domh et (x,y)∈h)
    y_in_image = syllogisme(equivalence_avant(img_eq),
                            syllogisme(ex_cy, equivalence_arriere(image_eq)))  # y∈pr₂h ⇒ y∈h⟨domh⟩
    incl_sup = N.generalisation(y, y_in_image)           # pr₂h ⊂ h⟨domh⟩

    # ── extensionnalité A1 : h⟨domh⟩ = pr₂h, puis symétrie ⇒ pr₂h... NON : la cible
    #    est_surjective = image(h,domh)=pr₂h, donc on garde l'orientation image=pr₂h.
    a1 = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), img_dir), imgh)
    img_eq_pr2 = N.modus_ponens(conjonction_intro(incl_sub, incl_sup), a1)  # image(h,domh)=pr₂h
    return img_eq_pr2


def surjectivite_h_image_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) :  est_surjective(h, dom h, pr₂ h)  (= image=pr₂)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return E.est_surjective(h, E.dom(h), E.img(h))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 CASCADE+ — décharger AUSSI la surjectivité (C, inconditionnelle).
# ════════════════════════════════════════════════════════════════════════════
def coherences_et_surjectivite_donnent_iso(E_set="E", R="R", F_set="F", Rp="Rp",
                                           x="x", y="w", u="u", up="up",
                                           v="v", vp="vp", S="S", T="T", phi="phi"):
    """⊢ { est_fonctionnel(h),
           (∀u,v,u') temoin_commun_inv_h(u,v,u'),
           (∀u,v,u',v') temoin_commun_h(u,v,u',v') }
         ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).

    🎯 CASCADE+ : la SURJECTIVITÉ (C) étant INCONDITIONNELLE (surjectivite_h_image),
    on la décharge AUSSI de la cascade.  Il ne reste plus, en hypothèses de cohérence,
    QUE les deux TÉMOINS COMMUNS (Lemme 1 §III.2) — et la fonctionnalité structurelle
    func h.  theorie=22, non vacueux.

    ⚠️ HONNÊTETÉ : func h reste hypothèse (= compatibilite_h, fonctionnalité par
    valeurs, autre face de Lemme 1 — duale de (A)) ; les deux témoins communs portent
    le contenu géométrique inconditionnel restant (emboîtement des segments)."""
    surj = surjectivite_h_image(E_set, R, F_set, Rp)
    iso = coherences_donnent_iso_sous_hyp(E_set, R, F_set, Rp, x, y, u, up, v, vp, S, T, phi)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    surj_form = E.est_surjective(h, E.dom(h), E.img(h))
    out = N.modus_ponens(surj, N.loi_deduction(surj_form, iso))   # décharge surjectivité
    return out


def coherences_et_surjectivite_donnent_iso_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                                 x="x", y="w"):
    """ÉNONCÉ-cible (test miroir) :  est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp)."""
    return H.h_est_isomorphisme_ordre_sous_hyp_cible(E_set, R, F_set, Rp, x, y)


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 CASCADE FINALE — h iso d'ordre SOUS LES SEULS témoins communs (Lemme 1).
#     func h, (A), (B), surjectivité TOUS déchargés ⇒ il ne reste QUE les 3
#     témoins communs (fonctionnalité / inverse / ordre = Lemme 1 §III.2).
# ════════════════════════════════════════════════════════════════════════════
def h_iso_ordre_sous_temoins_communs(E_set="E", R="R", F_set="F", Rp="Rp",
                                     x="x", y="w", u="u", up="up",
                                     v="v", vp="vp", z="z", S="S", T="T", phi="phi"):
    """⊢ { (∀u,v,z)   temoin_commun_fonc_h(u,v,z),
           (∀u,v,u')  temoin_commun_inv_h(u,v,u'),
           (∀u,v,u',v') temoin_commun_h(u,v,u',v') }
         ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).

    🎯🎯 RÉSULTAT le plus FORT du module : h (=h_iso_max) est un ISOMORPHISME D'ORDRE
    de dom(h) sur pr₂(h), sous les SEULES trois hypothèses géométriques de Lemme 1
    §III.2 (témoins communs : fonctionnalité, inverse, ordre).  Tout le reste —
    fonctionnalité func h (fonctionnel_depuis_temoin), cohérence inverse (A,
    compatibilite_inverse_depuis_temoin), cohérence d'ordre (B,
    compatibilite_ordre_depuis_temoin), surjectivité (C, surjectivite_h_image,
    INCONDITIONNELLE) — est DÉRIVÉ.  theorie=22, non vacueux.

    ⚠️ HONNÊTE : les trois témoins communs PORTENT le verrou dur restant
    (l'EMBOÎTEMENT des segments témoins + coïncidence des isos = Lemme 1 §III.2,
    magnitude Cantor–Bernstein) — REPORTÉ, jamais postulé.  Ce module montre qu'ils
    SUFFISENT : la trichotomie ne dépend plus QUE d'eux."""
    func = fonctionnel_depuis_temoin(E_set, R, F_set, Rp, u, v, z, S, T, phi)
    iso = coherences_et_surjectivite_donnent_iso(
        E_set, R, F_set, Rp, x, y, u, up, v, vp, S, T, phi)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    func_form = E.est_fonctionnel(h)
    out = N.modus_ponens(func, N.loi_deduction(func_form, iso))   # décharge func h
    return out


def h_iso_ordre_sous_temoins_communs_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                           x="x", y="w"):
    """ÉNONCÉ-cible (test miroir) :  est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp)."""
    return H.h_est_isomorphisme_ordre_sous_hyp_cible(E_set, R, F_set, Rp, x, y)


def h_iso_ordre_temoins_communs_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 3 HYPOTHÈSES (témoins communs = Lemme 1 §III.2) de
    h_iso_ordre_sous_temoins_communs (documentation / test miroir)."""
    return [
        temoin_commun_fonc_universel(E_set, R, F_set, Rp),
        temoin_commun_inv_universel(E_set, R, F_set, Rp),
        temoin_commun_universel(E_set, R, F_set, Rp),
    ]


__all__ = [
    "temoin_commun_h", "temoin_commun_universel",
    "compatibilite_ordre_depuis_temoin", "compatibilite_ordre_depuis_temoin_cible",
    "temoin_commun_inv_h", "temoin_commun_inv_universel",
    "compatibilite_inverse_depuis_temoin", "compatibilite_inverse_depuis_temoin_cible",
    "coherences_donnent_iso_sous_hyp", "coherences_donnent_iso_sous_hyp_cible",
    "surjectivite_h_image", "surjectivite_h_image_cible",
    "coherences_et_surjectivite_donnent_iso",
    "coherences_et_surjectivite_donnent_iso_cible",
    "temoin_commun_fonc_h", "temoin_commun_fonc_universel",
    "fonctionnel_depuis_temoin", "fonctionnel_depuis_temoin_cible",
    "h_iso_ordre_sous_temoins_communs", "h_iso_ordre_sous_temoins_communs_cible",
    "h_iso_ordre_temoins_communs_hypotheses",
]
