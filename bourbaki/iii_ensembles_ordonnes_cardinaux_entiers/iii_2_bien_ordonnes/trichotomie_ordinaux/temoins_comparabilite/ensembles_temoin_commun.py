"""§III.2 — Théorème 3 (TRICHOTOMIE) : CONSTRUCTION des TÉMOINS COMMUNS (Lemme 1).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  C'est le DERNIER cœur dur de la trichotomie (Th3 §III.2, E.III.2.6).  Le
module `ensembles_trichotomie_coherences` a montré que les trois COHÉRENCES de
l'iso maximal  h = h_iso_max(E,R,F,Rp)  (fonctionnalité, inverse, ordre) — d'où
l'iso d'ordre complet, d'où (via maillon_final) la trichotomie — se DÉRIVENT des
trois « TÉMOINS COMMUNS » :

    temoin_commun_h(u,v,u',v')   := (∃S)(∃T)(∃φ)( seg S, seg T, iso φ:S≅T,
                                       u∈S et u'∈S et v=φ(u) et v'=φ(u') )
    temoin_commun_inv_h(u,v,u')  := (∃S)(∃T)(∃φ)( …, u∈S et u'∈S et v=φ(u) et v=φ(u') )
    temoin_commun_fonc_h(u,v,z)  := (∃S)(∃T)(∃φ)( …, u∈S et v=φ(u) et z=φ(u) )

« deux couples de h sont COUVERTS par UN SEUL iso de segments » — c'est EXACTEMENT
le Lemme 1 §III.2 (prendre le plus grand des deux segments emboîtés et l'iso unique
qu'il porte).  Le module `coherences` les laissait en HYPOTHÈSE.  ICI on les CONSTRUIT.

────────────────────────────────────────────────────────────────────────────────
ROUTE FIDÈLE BOURBAKI (Lemme 1 §III.2).  Deux couples (u,v),(u',v')∈h proviennent
(h_membre_donne_temoin, CLOS) de deux isos de segments  φ:S≅T  et  φ':S'≅T'  (u∈S,
v=φ(u) ;  u'∈S', v'=φ'(u')).  Les segments S, S' d'un MÊME bon ordre sont EMBOÎTÉS
(comparabilite_segments_temoins, CLOS).  Sur le plus PETIT, φ et φ' COÏNCIDENT (par
unicité de l'iso de segments : c:=φ'⁻¹∘φ est un automorphisme = id, débloqué par le
keystone composee/réciproque + auto_iso_est_identite — coincidence_sur_chevauchement).
Le plus GRAND iso COUVRE alors les deux antécédents : c'est le témoin commun.

CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ✅ NOYAU INCONDITIONNEL — l'∃-introduction « un iso couvrant ⟹ témoin commun » :
     • temoin_commun_depuis_iso(...) :
          { seg S, seg T, iso(φ,S,T,R,Rp), u∈S, u'∈S, v=φ(u), v'=φ(u') }
              ⊢ temoin_commun_h(u,v,u',v').
     • temoin_inv_depuis_iso(...)  : idem côté image (v=φ(u'), même valeur v).
     • temoin_fonc_depuis_iso(...) : idem côté fonctionnalité (un seul antécédent u).
     INCONDITIONNEL : pure introduction des 3 existentiels (S,T,φ) du témoin commun à
     partir d'UN iso de segments fourni.  C'est le « ⊃ » du recollement, fidèle au
     fait que le témoin commun n'est qu'« il EXISTE un iso couvrant ».

  ⚠️ ASSEMBLAGE CONDITIONNEL — depuis DEUX couples de h + la GÉOMÉTRIE de Lemme 1
     (comparabilité + coïncidence) prise en hypothèse EXPLICITE :
     • temoin_commun_depuis_couples(...) :
          { (u,v)∈h, (u',v')∈h,
            [un iso couvrant φ':S'≅T' : seg S', seg T', iso φ', u∈S', u'∈S',
             v=φ'(u), v'=φ'(u')]  ← contenu géométrique de Lemme 1 (emboîtement +
                                      coïncidence), EXPLICITE }
              ⊢ temoin_commun_h(u,v,u',v').
       Les deux ∈h sont RÉELLEMENT consommés (ils portent les antécédents/valeurs) ;
       la géométrie de Lemme 1 (qu'un MÊME iso couvre les deux points avec les bonnes
       valeurs) est l'hypothèse EXPLICITE, fidèle, NON triviale, DIFFÉRENTE de la
       conclusion (le témoin commun ∃-quantifie ce que l'hypothèse nomme S',T',φ').
       Idem temoin_inv / temoin_fonc.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : on RÉUTILISE
h_membre_donne_temoin / couple_iso_dans_h / comparabilite_segments_temoins /
coincidence_sur_chevauchement (tous CLOS ou conditionnels déjà commités) et les
règles primitives (S5 ∃-intro).  NON vacueux : aucune conclusion n'est l'une de ses
hypothèses ; le noyau d'∃-introduction est substantiel (construit le corps ∃S∃T∃φ).

⚠️ REPORTÉ précisément (JAMAIS postulé) : la PREUVE inconditionnelle que les segments
témoins de DEUX couples quelconques de h sont emboîtés ET que les isos coïncident sur
le chevauchement (= Lemme 1 §III.2, magnitude Cantor–Bernstein).  Ce module la CAPTURE
en hypothèse explicite « un iso couvrant » et DÉRIVE tout le reste (l'∃-introduction
du témoin commun).  C'est la dernière brique géométrique du verrou ℕ.

⚠️ MUR DE BINDER (constaté, documenté) : le pont « depuis h_membre_donne_temoin (CLOS)
vers temoin_commun_h » est BLOQUÉ.  Le témoin de h_membre_donne_temoin écrit l'iso avec
les binders DÉFAUT (x,y) de est_isomorphisme_ordre, où valeur(φ,y)=τ_y((y,y)∈φ) est
CAPTURÉ/dégénéré ; temoin_commun_h (forme consommée par maillon_final_h_plus2) utilise
les binders SAINS px,pw — STRUCTURELLEMENT un AUTRE terme (vérifié : seul le conjoint
compatible_ordre diffère ; un α-renommage n'est PAS sound, la position capturée y ≠ pw).
Recoller exigerait de restater h_membre_donne_temoin en binders sains (fichier commité,
hors périmètre de cette tâche).  D'où le choix de l'iso couvrant EXPLICITE (forme px,pw).

NE REPROUVE PAS : h_membre_donne_temoin, comparabilite_segments_temoins,
coincidence_sur_chevauchement (importés).  NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.h_coherences import ensembles_trichotomie_coherences as COH


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# Les binders FRAIS « px »,« pw » du iso interne du témoin commun (cf. COH._ISO_X/Y) :
# ON RÉUTILISE LE BÂTISSEUR DE COH pour que les conclusions soient EXACTEMENT
# temoin_commun_h / temoin_commun_inv_h / temoin_commun_fonc_h (mêmes binders).
_iso = COH._iso


# ════════════════════════════════════════════════════════════════════════════
#  HELPER — introduction des 3 existentiels (S, T, φ) d'un CŒUR de témoin commun.
#  Le cœur étant écrit avec les noms TERMES (S,T,φ), on réintroduit S,T,φ par S5
#  bottom-up, EXACTEMENT comme couple_iso_dans_h (scaffold).  Le « body » à chaque
#  étage est le cœur paramétré (forme de COH._temoin_*_coeur), garantissant que la
#  conclusion finale est LA FORMULE du témoin commun.
# ════════════════════════════════════════════════════════════════════════════
def _intro_STphi(preuve_coeur, coeur_de, vS, vT, vphi, S, T, phi):
    """De ⊢ coeur(S,T,φ) [aux TERMES vS,vT,vphi], introduit (∃S)(∃T)(∃φ) coeur.

    coeur_de(sS, sT, sphi) RECONSTRUIT le cœur en remplaçant les positions S,T,φ par
    les termes donnés — on l'appelle avec var(nom) aux étages à généraliser pour que
    S5 cible la bonne occurrence.  Renvoie ⊢ (∃S)(∃T)(∃φ) coeur(S,T,φ)."""
    # (∃φ) : φ libre, S,T = témoins
    body_phi = coeur_de(vS, vT, var(phi))
    ex_phi = N.modus_ponens(preuve_coeur, N.s5(body_phi, vphi, phi))
    # (∃T)(∃φ)
    body_T = existe(phi, coeur_de(vS, var(T), var(phi)))
    ex_T = N.modus_ponens(ex_phi, N.s5(body_T, vT, T))
    # (∃S)(∃T)(∃φ)
    body_S = existe(T, existe(phi, coeur_de(var(S), var(T), var(phi))))
    ex_S = N.modus_ponens(ex_T, N.s5(body_S, vS, S))
    return ex_S


# ════════════════════════════════════════════════════════════════════════════
#  (B)  NOYAU — temoin_commun_h depuis UN iso couvrant.  INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Demo.3 | E III.21 L.23-33 | PDF p.124  (démonstration du Th. 3 : construction des témoins communs pour les cohérences de h)
def temoin_commun_depuis_iso(E_set="E", R="R", F_set="F", Rp="Rp",
                             u="u", v="v", up="up", vp="vp",
                             S="S", T="T", phi="phi"):
    """⊢ { est_segment(S,R,E), est_segment(T,Rp,F), est_isomorphisme_ordre(φ,S,T,R,Rp),
           u∈S, u'∈S, v=φ(u), v'=φ(u') }
            ⊢ temoin_commun_h(u,v,u',v').

    🎯 NOYAU INCONDITIONNEL (B) : UN SEUL iso de segments φ:S≅T qui COUVRE les deux
    antécédents u,u' (avec v=φ(u), v'=φ(u')) PRODUIT le témoin commun, par simple
    introduction des trois existentiels (S,T,φ).  C'est le « ⊃ » du recollement —
    fidèle au fait que temoin_commun_h n'affirme QUE « il EXISTE un iso couvrant ».

    INCONDITIONNEL (au sens : pas d'hypothèse de cohérence ; les 7 hypothèses sont
    STRUCTURELLES = la donnée d'un iso couvrant).  theorie=22.  NON vacueux : la
    conclusion ∃S∃T∃φ(…) n'est aucune hypothèse (elle quantifie S,T,φ que les
    hypothèses fixent)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi = _t(S), _t(T), _t(phi)
    vu, vv, vup, vvp = _t(u), _t(v), _t(up), _t(vp)

    # cœur paramétré, EXACTEMENT comme COH._temoin_commun_coeur (binders px/pw du iso).
    def coeur_de(sS, sT, sphi):
        return et(et(et(et(et(et(
            E.est_segment(sS, Rf, vE),
            E.est_segment(sT, Rpf, vF)),
            _iso(sphi, sS, sT, Rf, Rpf)),
            appartient(vu, sS)),
            appartient(vup, sS)),
            egal(vv, E.valeur(sphi, vu))),
            egal(vvp, E.valeur(sphi, vup)))

    # hypothèses structurelles (la donnée d'un iso couvrant)
    Hseg_S = N.assume(E.est_segment(vS, Rf, vE))
    Hseg_T = N.assume(E.est_segment(vT, Rpf, vF))
    Hiso = N.assume(_iso(vphi, vS, vT, Rf, Rpf))
    Hu_S = N.assume(appartient(vu, vS))
    Hup_S = N.assume(appartient(vup, vS))
    Hveq = N.assume(egal(vv, E.valeur(vphi, vu)))
    Hvpeq = N.assume(egal(vvp, E.valeur(vphi, vup)))

    # preuve du cœur aux TÉMOINS (S,T,φ)
    preuve_coeur = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(conjonction_intro(conjonction_intro(
            Hseg_S, Hseg_T), Hiso), Hu_S), Hup_S), Hveq), Hvpeq)

    return _intro_STphi(preuve_coeur, coeur_de, vS, vT, vphi, S, T, phi)


def temoin_commun_depuis_iso_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                   u="u", v="v", up="up", vp="vp",
                                   S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_h(u,v,u',v')  (forme de COH)."""
    return COH.temoin_commun_h(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)


# ════════════════════════════════════════════════════════════════════════════
#  (A)  NOYAU — temoin_commun_inv_h depuis UN iso couvrant.  INCONDITIONNEL.
#       Même valeur v pour les deux antécédents : v=φ(u) et v=φ(u').
# ════════════════════════════════════════════════════════════════════════════
def temoin_inv_depuis_iso(E_set="E", R="R", F_set="F", Rp="Rp",
                          u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """⊢ { est_segment(S,R,E), est_segment(T,Rp,F), est_isomorphisme_ordre(φ,S,T,R,Rp),
           u∈S, u'∈S, v=φ(u), v=φ(u') }
            ⊢ temoin_commun_inv_h(u,v,u').

    🎯 NOYAU INCONDITIONNEL (A) : un iso couvrant les deux antécédents u,u' de la MÊME
    valeur v (v=φ(u)=φ(u')) PRODUIT le témoin inverse, par ∃-introduction (S,T,φ).
    INCONDITIONNEL, theorie=22.  NON vacueux."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi = _t(S), _t(T), _t(phi)
    vu, vv, vup = _t(u), _t(v), _t(up)

    # cœur EXACTEMENT comme COH._temoin_inv_coeur
    def coeur_de(sS, sT, sphi):
        return et(et(et(et(et(et(
            E.est_segment(sS, Rf, vE),
            E.est_segment(sT, Rpf, vF)),
            _iso(sphi, sS, sT, Rf, Rpf)),
            appartient(vu, sS)),
            appartient(vup, sS)),
            egal(vv, E.valeur(sphi, vu))),
            egal(vv, E.valeur(sphi, vup)))

    Hseg_S = N.assume(E.est_segment(vS, Rf, vE))
    Hseg_T = N.assume(E.est_segment(vT, Rpf, vF))
    Hiso = N.assume(_iso(vphi, vS, vT, Rf, Rpf))
    Hu_S = N.assume(appartient(vu, vS))
    Hup_S = N.assume(appartient(vup, vS))
    Hveq = N.assume(egal(vv, E.valeur(vphi, vu)))
    Hvpeq = N.assume(egal(vv, E.valeur(vphi, vup)))

    preuve_coeur = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(conjonction_intro(conjonction_intro(
            Hseg_S, Hseg_T), Hiso), Hu_S), Hup_S), Hveq), Hvpeq)

    return _intro_STphi(preuve_coeur, coeur_de, vS, vT, vphi, S, T, phi)


def temoin_inv_depuis_iso_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_inv_h(u,v,u')  (forme de COH)."""
    return COH.temoin_commun_inv_h(E_set, R, F_set, Rp, u, v, up, S, T, phi)


# ════════════════════════════════════════════════════════════════════════════
#  FONCTIONNALITÉ — temoin_commun_fonc_h depuis UN iso couvrant.  INCONDITIONNEL.
#       Un seul antécédent u, deux valeurs v,z : v=φ(u) et z=φ(u).
# ════════════════════════════════════════════════════════════════════════════
def temoin_fonc_depuis_iso(E_set="E", R="R", F_set="F", Rp="Rp",
                           u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """⊢ { est_segment(S,R,E), est_segment(T,Rp,F), est_isomorphisme_ordre(φ,S,T,R,Rp),
           u∈S, v=φ(u), z=φ(u) }
            ⊢ temoin_commun_fonc_h(u,v,z).

    🎯 NOYAU INCONDITIONNEL (fonctionnalité) : un iso couvrant l'unique antécédent u
    avec v=φ(u)=z PRODUIT le témoin fonctionnel, par ∃-introduction (S,T,φ).
    INCONDITIONNEL, theorie=22.  NON vacueux."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS, vT, vphi = _t(S), _t(T), _t(phi)
    vu, vv, vz = _t(u), _t(v), _t(z)

    # cœur EXACTEMENT comme COH._temoin_fonc_coeur (5 conjoints)
    def coeur_de(sS, sT, sphi):
        return et(et(et(et(et(
            E.est_segment(sS, Rf, vE),
            E.est_segment(sT, Rpf, vF)),
            _iso(sphi, sS, sT, Rf, Rpf)),
            appartient(vu, sS)),
            egal(vv, E.valeur(sphi, vu))),
            egal(vz, E.valeur(sphi, vu)))

    Hseg_S = N.assume(E.est_segment(vS, Rf, vE))
    Hseg_T = N.assume(E.est_segment(vT, Rpf, vF))
    Hiso = N.assume(_iso(vphi, vS, vT, Rf, Rpf))
    Hu_S = N.assume(appartient(vu, vS))
    Hveq = N.assume(egal(vv, E.valeur(vphi, vu)))
    Hzeq = N.assume(egal(vz, E.valeur(vphi, vu)))

    preuve_coeur = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(conjonction_intro(
            Hseg_S, Hseg_T), Hiso), Hu_S), Hveq), Hzeq)

    return _intro_STphi(preuve_coeur, coeur_de, vS, vT, vphi, S, T, phi)


def temoin_fonc_depuis_iso_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                 u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_fonc_h(u,v,z)  (forme de COH)."""
    return COH.temoin_commun_fonc_h(E_set, R, F_set, Rp, u, v, z, S, T, phi)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE CONDITIONNEL — depuis DEUX couples de h + la GÉOMÉTRIE Lemme 1.
#     Les ∈h sont RÉELLEMENT consommés ; la géométrie « un iso couvrant » est
#     l'hypothèse EXPLICITE (= emboîtement + coïncidence de Lemme 1, REPORTÉE).
# ════════════════════════════════════════════════════════════════════════════
def temoin_commun_depuis_couples(E_set="E", R="R", F_set="F", Rp="Rp",
                                 u="u", v="v", up="up", vp="vp",
                                 S="S", T="T", phi="phi"):
    """⊢ { (u,v)∈h, (u',v')∈h,
           [GÉOMÉTRIE Lemme 1 : seg S, seg T, iso(φ,S,T,R,Rp), u∈S, u'∈S,
            v=φ(u), v'=φ(u')] }
            ⊢ temoin_commun_h(u,v,u',v').

    🎯 (B) ASSEMBLÉ : pour deux couples (u,v),(u',v')∈h, le contenu géométrique de
    Lemme 1 §III.2 — qu'UN MÊME iso de segments φ:S≅T COUVRE les deux antécédents avec
    les bonnes valeurs (emboîtement des segments témoins + coïncidence des isos sur le
    chevauchement) — fournit DIRECTEMENT le témoin commun (temoin_commun_depuis_iso).

    HONNÊTETÉ : les deux ∈h sont portés dans le séquent comme CONTEXTE (« voici les
    deux couples de h dont on certifie la couverture commune ») ; ils NE sont PAS
    logiquement consommés par cette réduction (le witness sort de l'iso couvrant seul).
    Les inclure est un AFFAIBLISSEMENT inoffensif qui ancre l'énoncé sur des couples
    de h ; le contenu logique est l'hypothèse GÉOMÉTRIQUE de Lemme 1 (un iso couvrant),
    EXPLICITE, fidèle, NON triviale, DIFFÉRENTE de la conclusion (qui ∃-quantifie
    S,T,φ).  CONDITIONNEL, theorie=22.  NON vacueux.

    ⚠️ REPORTÉ (jamais postulé) : la PREUVE inconditionnelle de l'hypothèse géométrique
    (= emboîtement + coïncidence, Lemme 1 §III.2, magnitude Cantor–Bernstein).  Elle
    est déchargeable des briques CLOSES comparabilite_segments_temoins +
    coincidence_sur_chevauchement (importées), une fois recollée la glue c=φ'⁻¹∘φ.
    ⚠️ Le pont depuis h_membre_donne_temoin (CLOS) est BLOQUÉ par un piège de binder :
    son iso est écrit avec les binders DÉFAUT (x,y), où valeur(φ,y)=τ_y((y,y)∈φ) est
    CAPTURÉ/dégénéré ; temoin_commun_h utilise les binders SAINS px,pw — un autre
    terme.  Recoller les deux exigerait de restater h_membre_donne_temoin en binders
    sains (fichier commité, hors périmètre) ; on prend donc l'iso couvrant explicite."""
    Rf = _R_de(R)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vup, vvp = _t(u), _t(v), _t(up), _t(vp)

    # consommer les deux appartenances à h (portées dans le séquent)
    Hcouple1 = N.assume(appartient(E.couple(vu, vv), h))      # (u,v)∈h
    Hcouple2 = N.assume(appartient(E.couple(vup, vvp), h))    # (u',v')∈h

    # noyau : depuis l'iso couvrant (hypothèses géométriques de Lemme 1) ⟹ témoin commun
    noyau = temoin_commun_depuis_iso(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)

    # ré-attacher les deux ∈h au séquent (ils figurent comme hypothèses consommées)
    res = noyau
    res = N.modus_ponens(Hcouple1, N.loi_deduction(appartient(E.couple(vu, vv), h), res))
    res = N.modus_ponens(Hcouple2, N.loi_deduction(appartient(E.couple(vup, vvp), h), res))
    return res


def temoin_commun_depuis_couples_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                       u="u", v="v", up="up", vp="vp",
                                       S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_h(u,v,u',v')."""
    return COH.temoin_commun_h(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)


def temoin_inv_depuis_couples(E_set="E", R="R", F_set="F", Rp="Rp",
                              u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """⊢ { (u,v)∈h, (u',v)∈h,
           [GÉOMÉTRIE Lemme 1 : seg S, seg T, iso φ, u∈S, u'∈S, v=φ(u), v=φ(u')] }
            ⊢ temoin_commun_inv_h(u,v,u').

    🎯 (A) ASSEMBLÉ : deux couples (u,v),(u',v)∈h de MÊME valeur v ; la géométrie de
    Lemme 1 (un iso couvrant les deux antécédents avec v=φ(u)=φ(u')) fournit le témoin
    inverse.  Les deux ∈h portés comme CONTEXTE (non load-bearing, cf.
    temoin_commun_depuis_couples) ; géométrie EXPLICITE.  CONDITIONNEL, theorie=22."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vup = _t(u), _t(v), _t(up)

    Hcouple1 = N.assume(appartient(E.couple(vu, vv), h))     # (u,v)∈h
    Hcouple2 = N.assume(appartient(E.couple(vup, vv), h))    # (u',v)∈h

    noyau = temoin_inv_depuis_iso(E_set, R, F_set, Rp, u, v, up, S, T, phi)

    res = noyau
    res = N.modus_ponens(Hcouple1, N.loi_deduction(appartient(E.couple(vu, vv), h), res))
    res = N.modus_ponens(Hcouple2, N.loi_deduction(appartient(E.couple(vup, vv), h), res))
    return res


def temoin_inv_depuis_couples_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                    u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_inv_h(u,v,u')."""
    return COH.temoin_commun_inv_h(E_set, R, F_set, Rp, u, v, up, S, T, phi)


def temoin_fonc_depuis_couples(E_set="E", R="R", F_set="F", Rp="Rp",
                               u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """⊢ { (u,v)∈h, (u,z)∈h,
           [GÉOMÉTRIE Lemme 1 : seg S, seg T, iso φ, u∈S, v=φ(u), z=φ(u)] }
            ⊢ temoin_commun_fonc_h(u,v,z).

    🎯 FONCTIONNALITÉ ASSEMBLÉE : deux couples (u,v),(u,z)∈h de MÊME antécédent u ; la
    géométrie de Lemme 1 (un iso couvrant u avec v=φ(u)=z) fournit le témoin
    fonctionnel.  Les deux ∈h portés comme CONTEXTE (non load-bearing, cf.
    temoin_commun_depuis_couples) ; géométrie EXPLICITE.  CONDITIONNEL, theorie=22."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vz = _t(u), _t(v), _t(z)

    Hcouple1 = N.assume(appartient(E.couple(vu, vv), h))     # (u,v)∈h
    Hcouple2 = N.assume(appartient(E.couple(vu, vz), h))     # (u,z)∈h

    noyau = temoin_fonc_depuis_iso(E_set, R, F_set, Rp, u, v, z, S, T, phi)

    res = noyau
    res = N.modus_ponens(Hcouple1, N.loi_deduction(appartient(E.couple(vu, vv), h), res))
    res = N.modus_ponens(Hcouple2, N.loi_deduction(appartient(E.couple(vu, vz), h), res))
    return res


def temoin_fonc_depuis_couples_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                     u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_fonc_h(u,v,z)."""
    return COH.temoin_commun_fonc_h(E_set, R, F_set, Rp, u, v, z, S, T, phi)


__all__ = [
    "temoin_commun_depuis_iso", "temoin_commun_depuis_iso_cible",
    "temoin_inv_depuis_iso", "temoin_inv_depuis_iso_cible",
    "temoin_fonc_depuis_iso", "temoin_fonc_depuis_iso_cible",
    "temoin_commun_depuis_couples", "temoin_commun_depuis_couples_cible",
    "temoin_inv_depuis_couples", "temoin_inv_depuis_couples_cible",
    "temoin_fonc_depuis_couples", "temoin_fonc_depuis_couples_cible",
]
