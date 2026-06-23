"""§III.2 — Théorème 3 (TRICHOTOMIE) : TÉMOIN COMMUN depuis DEUX COUPLES de h.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  C'est le VRAI Lemme 1 §III.2 (E.III.2.6), pris « par couples de h » : à partir
de DEUX couples  (u,v)∈h  et  (u',v')∈h  de l'iso maximal  h = h_iso_max(E,R,F,Rp)
(union des graphes d'iso de segments isomorphes), produire le TÉMOIN COMMUN

    temoin_commun_h(u,v,u',v')  :=  (∃S)(∃T)(∃φ)( seg S, seg T, iso φ:S≅T,
                                       u∈S et u'∈S et v=φ(u) et v'=φ(u') )

« UN SEUL iso de segments couvre les DEUX antécédents avec les bonnes valeurs ».

Le module `ensembles_temoin_commun` (commité) le livrait à partir d'un iso couvrant
EXPLICITE (`temoin_commun_depuis_iso`, INCONDITIONNEL) puis d'un assemblage où les deux
∈h n'étaient PAS load-bearing (`temoin_commun_depuis_couples` — honnêteté documentée).
ICI on va plus loin : les deux ∈h sont RÉELLEMENT CONSOMMÉS via `h_membre_donne_temoin`
(CLOS), qui EXTRAIT de chaque couple son iso de segments témoin.

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (salvage fort GRADUÉ, honnête, theorie=22, rien postulé) :

  ✅✅ NOYAU INCONDITIONNEL — le CAS DIAGONAL du Lemme 1 (u'=u, v'=v), TOTALEMENT
     fermé à partir d'UN SEUL couple de h :
       • `temoin_commun_diagonal_depuis_h(u,v)` :
            { (u,v) ∈ h }  ⊢  temoin_commun_h(u,v,u,v).
       • `temoin_inv_diagonal_depuis_h(u,v)` :
            { (u,v) ∈ h }  ⊢  temoin_commun_inv_h(u,v,u).
       • `temoin_fonc_diagonal_depuis_h(u,v)` :
            { (u,v) ∈ h }  ⊢  temoin_commun_fonc_h(u,v,v).
     Le SEUL et UNIQUE ∈h est RÉELLEMENT load-bearing : on EXTRAIT son iso témoin
     via `h_membre_donne_temoin` (CLOS), on DÉDOUBLE à l'intérieur de l'existentiel
     l'antécédent u et la valeur v (le même iso couvre u « deux fois »), puis on
     remonte à travers les trois ∃ par `monotonie_existe`.  AUCUNE hypothèse de
     cohérence/géométrie : pour deux couples ÉGAUX, l'iso d'UN couple suffit
     trivialement à couvrir l'autre — c'est le cas dégénéré (mais NON vacueux) du
     Lemme 1, prouvé INCONDITIONNELLEMENT.  C'est la première fois que le témoin
     commun sort DIRECTEMENT de l'appartenance à h (pont scaffold → témoin).

  ⚠️ RÉDUCTION HONNÊTE — le CAS GÉNÉRAL (u',v') ≠ (u,v) du Lemme 1, où les deux ∈h
     sont CONSOMMÉS via `h_membre_donne_temoin` (CLOS) et où la seule chose reportée
     est l'étape de FUSION (emboîtement des segments témoins + coïncidence des isos
     sur le chevauchement = cœur Cantor–Bernstein) :
       • `temoin_commun_depuis_deux_h_couples(u,v,u',v')` :
            { (u,v) ∈ h,  (u',v') ∈ h,
              FUSION :  temoin₁(u,v) ⇒ ( (u',v')∈h ⇒ temoin_commun_h(u,v,u',v') ) }
                ⊢ temoin_commun_h(u,v,u',v').
         où  temoin₁(u,v) := (∃S)(∃T)(∃φ)( seg S, seg T, iso φ, u∈S, v=φ(u) )  est le
         témoin de segment EXTRAIT de (u,v)∈h (réciproque de couple_iso_dans_h).
       Les DEUX ∈h sont VRAIMENT load-bearing : (u,v)∈h produit temoin₁ par
       `h_membre_donne_temoin` (CLOS), la FUSION le combine avec (u',v')∈h.  La
       FUSION porte EXACTEMENT le contenu géométrique reporté (Lemme 1) ; elle est
       EXPLICITE, fidèle, NON triviale, DIFFÉRENTE de la conclusion.  Idem inv/fonc.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  RÉUTILISE (NE REPROUVE PAS)
`h_membre_donne_temoin` (CLOS, scaffold), `temoin_commun_h` / `temoin_commun_inv_h` /
`temoin_commun_fonc_h` (formules de COH), `monotonie_existe` (tactique dérivée).
NON vacueux : aucune conclusion n'est l'une de ses hypothèses.

────────────────────────────────────────────────────────────────────────────────
⚠️ REPORTÉ précisément (JAMAIS postulé) — pour le cas GÉNÉRAL : la PREUVE
inconditionnelle de la FUSION (= les segments témoins de DEUX couples QUELCONQUES de
h sont emboîtés ET les isos coïncident sur le chevauchement, Lemme 1 §III.2, magnitude
Cantor–Bernstein).  Elle est déchargeable, brique par brique, de
`comparabilite_segments_temoins` (CLOS) + `restriction_compatible_ordre` (CLOS) +
`coincidence_sur_chevauchement` / `coincidence_depuis_isos` (CLOS sous géométrie) —
le résidu restant est le pont représentationnel « liant-valeur » + « binder composite »
documenté dans ensembles_coincidence_decharge.  Ce module CAPTURE ce résidu dans la
SEULE hypothèse de FUSION et DÉRIVE tout le reste (l'extraction + l'enchaînement).
Le cas DIAGONAL, lui, ne le rencontre PAS (un couple unique) : INCONDITIONNEL.

NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import monotonie_existe
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_coherences as COH


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# On RÉUTILISE le bâtisseur d'iso de COH (binders SAINS px/pw) : les conclusions sont
# EXACTEMENT temoin_commun_h / temoin_commun_inv_h / temoin_commun_fonc_h.
_iso = COH._iso


# ════════════════════════════════════════════════════════════════════════════
#  HELPER — témoin de segment EXTRAIT de (u,v)∈h (corps existentiel de
#  h_membre_donne_temoin, = réciproque par couple de couple_iso_dans_h).
# ════════════════════════════════════════════════════════════════════════════
def _temoin1_ex(E_set, R, F_set, Rp, u, v, S="S", T="T", phi="phi"):
    """(∃S)(∃T)(∃φ)( seg S, seg T, iso φ:S≅T, u∈S, v=φ(u) ).

    Le témoin de segment d'UN couple (u,v) — EXACTEMENT le corps existentiel produit
    par h_membre_donne_temoin (cf. scaffold `_h_parts`)."""
    _, temoin = TS._h_parts(E_set, R, F_set, Rp, _t(u), _t(v), S, T, phi)
    return temoin


def _coeur1(E_set, R, F_set, Rp, u, v, vS, vT, vphi):
    """Le CŒUR (sans les ∃) de _temoin1_ex aux termes vS,vT,vphi :
       seg S, seg T, iso φ, u∈S, v=φ(u), func φ, dom φ=S, φ⊂S×T
       (forme de _h_parts STRENGTHENED, binders px/pw).

    ⚠️ ARCHITECTURE func/dom : DOIT mirroir EXACTEMENT TS._h_parts (8 conjoints : les
    5 originaux + func + dom + graphe au niveau EXTERNE), sinon _temoin1_ex (qui
    réutilise _h_parts) et _coeur1 divergent et la fusion casse."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vu, vv = _t(u), _t(v)
    coeur5 = et(et(et(et(
        E.est_segment(vS, Rf, vE),
        E.est_segment(vT, Rpf, vF)),
        _iso(vphi, vS, vT, Rf, Rpf)),
        appartient(vu, vS)),
        egal(vv, E.valeur(vphi, vu)))
    # ── 3 conjoints « φ APPLICATION » appendus AU NIVEAU EXTERNE (les 5 d'abord) ──
    return et(et(et(coeur5,
        E.est_fonctionnel(vphi)),
        egal(E.dom(vphi), vS)),
        inclus(vphi, E.produit(vS, vT)))


def _coeur5_de(Hc8):
    """De ⊢ coeur8 (= _coeur1 STRENGTHENED), pèle les 3 conjoints externes func/dom/
    graphe et retourne ⊢ coeur5 (les 5 conjoints originaux : seg,seg,iso,u∈S,v=φ(u)).

    coeur8 = et(et(et(coeur5, func), dom), graphe).  On élimine 3 fois à gauche."""
    return conjonction_elim_gauche(conjonction_elim_gauche(conjonction_elim_gauche(Hc8)))


# ════════════════════════════════════════════════════════════════════════════
#  ✅✅ NOYAU INCONDITIONNEL — CAS DIAGONAL (u'=u, v'=v) du Lemme 1.
#  temoin_commun_h(u,v,u,v) sort DIRECTEMENT d'UN SEUL (u,v)∈h.
# ════════════════════════════════════════════════════════════════════════════
def temoin_commun_diagonal_depuis_h(E_set="E", R="R", F_set="F", Rp="Rp",
                                    u="u", v="v", S="S", T="T", phi="phi"):
    """⊢ { (u,v) ∈ h }  ⊢  temoin_commun_h(u,v,u,v).

    🎯🎯 CAS DIAGONAL du Lemme 1 §III.2, INCONDITIONNEL.  Le SEUL ∈h est RÉELLEMENT
    consommé : `h_membre_donne_temoin` (CLOS) EXTRAIT de (u,v)∈h son iso de segments
    témoin  φ:S≅T  (u∈S, v=φ(u)) ; ce MÊME iso couvre u « deux fois » (u∈S et u∈S,
    v=φ(u) et v=φ(u)), donc témoigne de temoin_commun_h(u,v,u,v).

    PREUVE.  Du CŒUR  coeur1 = (seg S, seg T, iso φ, u∈S, v=φ(u))  on DÉDOUBLE u∈S et
    v=φ(u) pour obtenir  coeur_diag = (seg S, seg T, iso φ, u∈S, u∈S, v=φ(u), v=φ(u))
    (= cœur de temoin_commun_h(u,v,u,v)) : c'est une implication CLOSE de corps.  On la
    remonte à travers (∃φ)(∃T)(∃S) par `monotonie_existe`, d'où  temoin1(u,v) ⇒
    temoin_commun_h(u,v,u,v).  Enfin (u,v)∈h ⇒ temoin1(u,v) (h_membre_donne_temoin,
    CLOS) puis modus ponens.  INCONDITIONNEL (1 seule hypothèse = (u,v)∈h, load-bearing).
    theorie=22.  NON vacueux : temoin_commun_h(u,v,u,v) ≠ (u,v)∈h."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vu, vv = _t(u), _t(v)
    vS, vT, vphi = var(S), var(T), var(phi)

    # ── implication de corps  coeur1 ⇒ coeur_diag  (CLOSE) ──────────────────────
    Hc8 = N.assume(_coeur1(E_set, R, F_set, Rp, u, v, vS, vT, vphi))
    Hc = _coeur5_de(Hc8)                           # pèle func/dom/graphe → coeur5
    c_v = conjonction_elim_droite(Hc)              # v=φ(u)
    c_rest = conjonction_elim_gauche(Hc)           # seg S, seg T, iso, u∈S
    c_uS = conjonction_elim_droite(c_rest)         # u∈S
    c_segiso = conjonction_elim_gauche(c_rest)     # seg S, seg T, iso
    c_segS = conjonction_elim_gauche(conjonction_elim_gauche(c_segiso))   # seg S
    c_segT = conjonction_elim_droite(conjonction_elim_gauche(c_segiso))   # seg T
    c_iso = conjonction_elim_droite(c_segiso)                             # iso φ
    # coeur_diag = ((((((seg S, seg T), iso), u∈S), u∈S), v=φ(u)), v=φ(u))
    diag_proof = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(conjonction_intro(conjonction_intro(
            c_segS, c_segT), c_iso), c_uS), c_uS), c_v), c_v)
    imp = N.loi_deduction(
        _coeur1(E_set, R, F_set, Rp, u, v, vS, vT, vphi), diag_proof)   # coeur1 ⇒ coeur_diag

    # ── remontée à travers les 3 ∃ : temoin1(u,v) ⇒ temoin_commun_h(u,v,u,v) ────
    imp_phi = monotonie_existe(imp, phi)
    imp_T = monotonie_existe(imp_phi, T)
    imp_S = monotonie_existe(imp_T, S)             # temoin1(u,v) ⇒ temoin_commun_h(u,v,u,v)

    # ── (u,v)∈h ⇒ temoin1(u,v) (h_membre_donne_temoin, CLOS) ────────────────────
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    hmdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "u", "v", S, T, phi)
    hmdt_inst = instancie(instancie(hmdt, vu), vv)
    Hcouple = N.assume(appartient(E.couple(vu, vv), h))
    temoin1 = N.modus_ponens(Hcouple, hmdt_inst)   # temoin1(u,v)  [hyp : (u,v)∈h]
    return N.modus_ponens(temoin1, imp_S)          # temoin_commun_h(u,v,u,v)  [hyp : (u,v)∈h]


def temoin_commun_diagonal_depuis_h_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                          u="u", v="v", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_h(u,v,u,v)."""
    return COH.temoin_commun_h(E_set, R, F_set, Rp, u, v, u, v, S, T, phi)


def temoin_inv_diagonal_depuis_h(E_set="E", R="R", F_set="F", Rp="Rp",
                                 u="u", v="v", S="S", T="T", phi="phi"):
    """⊢ { (u,v) ∈ h }  ⊢  temoin_commun_inv_h(u,v,u).

    🎯 CAS DIAGONAL (côté inverse) du Lemme 1, INCONDITIONNEL.  temoin_commun_inv_h(u,v,u)
    a le MÊME cœur que temoin_commun_h(u,v,u,v) (deux antécédents égaux u, même valeur v) ;
    il sort donc IDENTIQUEMENT du seul (u,v)∈h.  theorie=22, NON vacueux."""
    # même cœur que la diagonale : temoin_commun_inv_h(u,v,u) == temoin_commun_h(u,v,u,v)
    return temoin_commun_diagonal_depuis_h(E_set, R, F_set, Rp, u, v, S, T, phi)


def temoin_inv_diagonal_depuis_h_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                       u="u", v="v", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_inv_h(u,v,u)."""
    return COH.temoin_commun_inv_h(E_set, R, F_set, Rp, u, v, u, S, T, phi)


def temoin_fonc_diagonal_depuis_h(E_set="E", R="R", F_set="F", Rp="Rp",
                                  u="u", v="v", S="S", T="T", phi="phi"):
    """⊢ { (u,v) ∈ h }  ⊢  temoin_commun_fonc_h(u,v,v).

    🎯 CAS DIAGONAL (côté fonctionnalité) du Lemme 1, INCONDITIONNEL.  temoin_commun_fonc_h(u,v,v)
    := (∃S,T,φ)( seg S, seg T, iso φ, u∈S, v=φ(u), v=φ(u) ) : UN antécédent u, deux valeurs
    ÉGALES v.  Il sort du seul (u,v)∈h en DÉDOUBLANT la valeur v=φ(u) (sans dédoubler u∈S).
    theorie=22, NON vacueux : temoin_commun_fonc_h(u,v,v) ≠ (u,v)∈h."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vu, vv = _t(u), _t(v)
    vS, vT, vphi = var(S), var(T), var(phi)

    # cœur de temoin_commun_fonc_h(u,v,v) : (seg S, seg T, iso, u∈S, v=φ(u), v=φ(u))
    Hc8 = N.assume(_coeur1(E_set, R, F_set, Rp, u, v, vS, vT, vphi))
    Hc = _coeur5_de(Hc8)                           # pèle func/dom/graphe → coeur5
    c_v = conjonction_elim_droite(Hc)              # v=φ(u)
    c_rest = conjonction_elim_gauche(Hc)           # seg S, seg T, iso, u∈S  (= 4 conjoints)
    # coeur_fonc = (((( (seg S, seg T, iso), u∈S ), v=φ(u)), v=φ(u))  [reprend c_rest entier]
    fonc_proof = conjonction_intro(conjonction_intro(c_rest, c_v), c_v)
    imp = N.loi_deduction(
        _coeur1(E_set, R, F_set, Rp, u, v, vS, vT, vphi), fonc_proof)  # coeur1 ⇒ coeur_fonc

    imp_phi = monotonie_existe(imp, phi)
    imp_T = monotonie_existe(imp_phi, T)
    imp_S = monotonie_existe(imp_T, S)             # temoin1(u,v) ⇒ temoin_commun_fonc_h(u,v,v)

    h = TS.h_iso_max(E_set, R, F_set, Rp)
    hmdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "u", "v", S, T, phi)
    hmdt_inst = instancie(instancie(hmdt, vu), vv)
    Hcouple = N.assume(appartient(E.couple(vu, vv), h))
    temoin1 = N.modus_ponens(Hcouple, hmdt_inst)
    return N.modus_ponens(temoin1, imp_S)          # temoin_commun_fonc_h(u,v,v)  [hyp : (u,v)∈h]


def temoin_fonc_diagonal_depuis_h_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                        u="u", v="v", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_fonc_h(u,v,v)."""
    return COH.temoin_commun_fonc_h(E_set, R, F_set, Rp, u, v, v, S, T, phi)


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ RÉDUCTION HONNÊTE — CAS GÉNÉRAL : DEUX couples de h CONSOMMÉS via
#  h_membre_donne_temoin ; seule la FUSION (Lemme 1 dur) reste hypothèse.
# ════════════════════════════════════════════════════════════════════════════
def fusion_hyp(E_set="E", R="R", F_set="F", Rp="Rp",
               u="u", v="v", up="up", vp="vp", S="S", T="T", phi="phi"):
    """FORMULE de FUSION (Lemme 1 §III.2, contenu géométrique reporté) :

        temoin₁(u,v)  ⇒  ( (u',v')∈h  ⇒  temoin_commun_h(u,v,u',v') )

    où temoin₁(u,v) := (∃S)(∃T)(∃φ)( seg S, seg T, iso φ:S≅T, u∈S, v=φ(u) ) est le
    témoin de segment EXTRAIT de (u,v)∈h.

    « connaissant l'iso témoin du PREMIER couple ET le second couple (u',v')∈h, UN
    SEUL iso de segments couvre les DEUX antécédents ».  C'est EXACTEMENT le contenu
    de l'emboîtement des segments + coïncidence des isos (Lemme 1, Cantor–Bernstein),
    formulé pour être consommé après extraction du premier témoin.  Posé EXPLICITE,
    jamais comme théorème.  VRAI, non trivial, DIFFÉRENT de temoin_commun_h."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vup, vvp = _t(up), _t(vp)
    t1 = _temoin1_ex(E_set, R, F_set, Rp, u, v, S, T, phi)
    c2 = appartient(E.couple(vup, vvp), h)
    tch = COH.temoin_commun_h(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)
    return impl(t1, impl(c2, tch))


def temoin_commun_depuis_deux_h_couples(E_set="E", R="R", F_set="F", Rp="Rp",
                                        u="u", v="v", up="up", vp="vp",
                                        S="S", T="T", phi="phi"):
    """⊢ { (u,v) ∈ h,  (u',v') ∈ h,  FUSION } ⊢ temoin_commun_h(u,v,u',v').

    🎯 CAS GÉNÉRAL du Lemme 1 §III.2 (E.III.2.6) — les DEUX couples de h sont
    RÉELLEMENT consommés :
      • (u,v)∈h ⇒ temoin₁(u,v)   par  h_membre_donne_temoin (CLOS) — EXTRACTION du
        premier iso témoin (réciproque par couple de couple_iso_dans_h) ;
      • la FUSION (`fusion_hyp`, contenu géométrique de Lemme 1 — emboîtement +
        coïncidence, REPORTÉ) combine temoin₁ avec (u',v')∈h pour donner UN iso
        couvrant les deux antécédents, i.e. temoin_commun_h(u,v,u',v').

    Les deux ∈h sont LOAD-BEARING (sans eux, ni temoin₁ ni la conséquence de la FUSION).
    CONDITIONNEL à la SEULE hypothèse de FUSION (= Lemme 1 dur, explicite), theorie=22.
    NON vacueux : temoin_commun_h(u,v,u',v') n'est aucune hypothèse.

    ⚠️ REPORTÉ : la PREUVE de la FUSION (emboîtement des segments témoins de DEUX
    couples QUELCONQUES + coïncidence des isos, Lemme 1, magnitude Cantor–Bernstein),
    déchargeable des bricks CLOS comparabilite_segments_temoins / restriction_compatible_
    ordre / coincidence_sur_chevauchement (le résidu = pont représentationnel liant-valeur,
    documenté dans ensembles_coincidence_decharge)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vup, vvp = _t(u), _t(v), _t(up), _t(vp)

    # ── EXTRACTION : (u,v)∈h ⇒ temoin₁(u,v)  (h_membre_donne_temoin, CLOS) ───────
    hmdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "u", "v", S, T, phi)
    hmdt_inst = instancie(instancie(hmdt, vu), vv)
    Hc1 = N.assume(appartient(E.couple(vu, vv), h))
    t1 = N.modus_ponens(Hc1, hmdt_inst)            # temoin₁(u,v)  [hyp : (u,v)∈h]

    # ── FUSION : temoin₁ ⇒ ( (u',v')∈h ⇒ temoin_commun_h ) ──────────────────────
    HM = N.assume(fusion_hyp(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi))
    step = N.modus_ponens(t1, HM)                  # (u',v')∈h ⇒ temoin_commun_h  [hyps : (u,v)∈h, FUSION]
    Hc2 = N.assume(appartient(E.couple(vup, vvp), h))
    return N.modus_ponens(Hc2, step)               # temoin_commun_h(u,v,u',v')


def temoin_commun_depuis_deux_h_couples_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                              u="u", v="v", up="up", vp="vp",
                                              S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_h(u,v,u',v')."""
    return COH.temoin_commun_h(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)


# ── variantes inverse / fonctionnalité du cas général (mêmes FUSION dédiées) ─────
def fusion_inv_hyp(E_set="E", R="R", F_set="F", Rp="Rp",
                   u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """FORMULE de FUSION (côté inverse) :
        temoin₁(u,v) ⇒ ( (u',v)∈h ⇒ temoin_commun_inv_h(u,v,u') ).  (Lemme 1, REPORTÉ.)"""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vup, vv = _t(up), _t(v)
    t1 = _temoin1_ex(E_set, R, F_set, Rp, u, v, S, T, phi)
    c2 = appartient(E.couple(vup, vv), h)
    tinv = COH.temoin_commun_inv_h(E_set, R, F_set, Rp, u, v, up, S, T, phi)
    return impl(t1, impl(c2, tinv))


def temoin_inv_depuis_deux_h_couples(E_set="E", R="R", F_set="F", Rp="Rp",
                                     u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """⊢ { (u,v)∈h, (u',v)∈h, FUSION_inv } ⊢ temoin_commun_inv_h(u,v,u').

    🎯 CAS GÉNÉRAL (côté inverse) du Lemme 1 : deux couples (u,v),(u',v)∈h de MÊME valeur
    v, tous deux CONSOMMÉS (extraction de (u,v)∈h via h_membre_donne_temoin CLOS + FUSION
    avec (u',v)∈h).  CONDITIONNEL à la FUSION (REPORTÉ), theorie=22, NON vacueux."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vup = _t(u), _t(v), _t(up)
    hmdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "u", "v", S, T, phi)
    hmdt_inst = instancie(instancie(hmdt, vu), vv)
    Hc1 = N.assume(appartient(E.couple(vu, vv), h))
    t1 = N.modus_ponens(Hc1, hmdt_inst)
    HM = N.assume(fusion_inv_hyp(E_set, R, F_set, Rp, u, v, up, S, T, phi))
    step = N.modus_ponens(t1, HM)
    Hc2 = N.assume(appartient(E.couple(vup, vv), h))
    return N.modus_ponens(Hc2, step)


def temoin_inv_depuis_deux_h_couples_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                           u="u", v="v", up="up", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_inv_h(u,v,u')."""
    return COH.temoin_commun_inv_h(E_set, R, F_set, Rp, u, v, up, S, T, phi)


def fusion_fonc_hyp(E_set="E", R="R", F_set="F", Rp="Rp",
                    u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """FORMULE de FUSION (côté fonctionnalité) :
        temoin₁(u,v) ⇒ ( (u,z)∈h ⇒ temoin_commun_fonc_h(u,v,z) ).  (Lemme 1, REPORTÉ.)"""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vz = _t(u), _t(z)
    t1 = _temoin1_ex(E_set, R, F_set, Rp, u, v, S, T, phi)
    c2 = appartient(E.couple(vu, vz), h)
    tfonc = COH.temoin_commun_fonc_h(E_set, R, F_set, Rp, u, v, z, S, T, phi)
    return impl(t1, impl(c2, tfonc))


def temoin_fonc_depuis_deux_h_couples(E_set="E", R="R", F_set="F", Rp="Rp",
                                      u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """⊢ { (u,v)∈h, (u,z)∈h, FUSION_fonc } ⊢ temoin_commun_fonc_h(u,v,z).

    🎯 CAS GÉNÉRAL (côté fonctionnalité) du Lemme 1 : deux couples (u,v),(u,z)∈h de MÊME
    antécédent u, tous deux CONSOMMÉS.  CONDITIONNEL à la FUSION (REPORTÉ), theorie=22."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    vu, vv, vz = _t(u), _t(v), _t(z)
    hmdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "u", "v", S, T, phi)
    hmdt_inst = instancie(instancie(hmdt, vu), vv)
    Hc1 = N.assume(appartient(E.couple(vu, vv), h))
    t1 = N.modus_ponens(Hc1, hmdt_inst)
    HM = N.assume(fusion_fonc_hyp(E_set, R, F_set, Rp, u, v, z, S, T, phi))
    step = N.modus_ponens(t1, HM)
    Hc2 = N.assume(appartient(E.couple(vu, vz), h))
    return N.modus_ponens(Hc2, step)


def temoin_fonc_depuis_deux_h_couples_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                            u="u", v="v", z="z", S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  temoin_commun_fonc_h(u,v,z)."""
    return COH.temoin_commun_fonc_h(E_set, R, F_set, Rp, u, v, z, S, T, phi)


__all__ = [
    # ✅✅ diagonal INCONDITIONNEL (1 hyp = un ∈h)
    "temoin_commun_diagonal_depuis_h", "temoin_commun_diagonal_depuis_h_cible",
    "temoin_inv_diagonal_depuis_h", "temoin_inv_diagonal_depuis_h_cible",
    "temoin_fonc_diagonal_depuis_h", "temoin_fonc_diagonal_depuis_h_cible",
    # ⚠️ général (deux ∈h consommés + FUSION reportée)
    "fusion_hyp", "temoin_commun_depuis_deux_h_couples",
    "temoin_commun_depuis_deux_h_couples_cible",
    "fusion_inv_hyp", "temoin_inv_depuis_deux_h_couples",
    "temoin_inv_depuis_deux_h_couples_cible",
    "fusion_fonc_hyp", "temoin_fonc_depuis_deux_h_couples",
    "temoin_fonc_depuis_deux_h_couples_cible",
]
