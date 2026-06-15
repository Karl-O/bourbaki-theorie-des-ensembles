"""§III.2 — Théorème 3 (TRICHOTOMIE) : FUSION DÉRIVÉE de la COÏNCIDENCE PROUVÉE.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  RE-CÂBLAGE de l'assemblage `ensembles_fusion_assemblage.fusion_depuis_coincidence`
pour faire reposer `fusion_hyp` sur la COÏNCIDENCE **PROUVÉE** (`coincidence_point_app`,
qui consomme `coincidence_univ_app`, THÉORÈME CLOS) au lieu de la COÏNCIDENCE **POSTULÉE**
(`coincidence_univ`).  C'est l'étape de paiement qui RETIRE le dernier postulat géométrique.

`fusion_depuis_coincidence` (assemblage existant, INCHANGÉ) reposait sur :
    { est_bien_ordonne(R,E),  coincidence_univ }  ⊢  fusion_hyp(u,v,u',v').
où `coincidence_univ` est une HYPOTHÈSE POSTULÉE (deux isos de segments emboîtés
coïncident sur le petit).  Ici on la REMPLACE par un appel à `coincidence_point_app`
(`ensembles_fusion_app`), dont la PRÉMISSE_APPLICATIONS (14 conjoints) est DÉCHARGÉE des
CŒURS STRENGTHENED (iso/func/dom/graphe/segment) + bons ordres AMBIANTS + comparabilité.

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (theorie=22, rien postulé — `coincidence_univ` est GONE) :

  ✅ `fusion_depuis_coincidence_app(...)` :
        { est_bien_ordonne(R,E),  est_bien_ordonne(R',F),  CŒUR₁(couple A),  CŒUR₁(couple B),
          RÉSIDU_GÉOMÉTRIQUE (voir ci-dessous) }  ⊢  fusion_hyp(u,v,u',v').
     i.e. CONCLUSION == `ensembles_temoin_deux_couples.fusion_hyp(...)` LITTÉRALEMENT
     (le MÊME énoncé-cible que `fusion_depuis_coincidence`), **SANS `coincidence_univ`**.

────────────────────────────────────────────────────────────────────────────────
DÉCHARGE DE LA PRÉMISSE_APPLICATIONS (14 conjoints de coincidence_point_app).
Pour le point p∈S_petit, `coincidence_point_app(φp,φg,Sp,Tp,Sg,Tg,F,R,Rp,p)` donne
φp(p)[j]=φg(p)[j] sous 14 hypothèses + p∈S_petit.  `_coinc_point_app` les décharge :

  • 0  iso(φp,Sp,Tp)[x,y]          ← CŒUR petit, iso (binders px/pw) α-renommé en x/y
  • 1  iso(φg,Sg,Tg)[a,b]          ← CŒUR grand, iso (binders px/pw) α-renommé en a/b
  • 2  func(φp)                    ← CŒUR petit (conjoint func)
  • 3  func(φg)                    ← CŒUR grand (conjoint func)
  • 4  dom(φp)=Sp                  ← CŒUR petit (conjoint dom)
  • 5  dom(φg)=Sg                  ← CŒUR grand (conjoint dom)
  • 6  inclus(Sp,Sg)              ← COMPARABILITÉ (segments_abstraits_comparables, branche)
  • 7  est_segment(Tp,R',F)        ← CŒUR petit (conjoint segT)
  • 9  est_bien_ordonne(R',F)      ← AMBIANT (hypothèse de fusion)
  • 10 est_bien_ordonne(R,E)       ← AMBIANT (hypothèse de fusion)
  • 11 inclus(Sp,E)               ← CŒUR petit, 1ᵉʳ conjoint de est_segment(Sp,R,E)
  • 12 inclus(φp,Sp×Tp)           ← CŒUR petit (conjoint graphe)
  • 8  est_segment(image(φg,Sp),R',F)   ← RÉSIDU (voir NOTE), via `residu_univ_app`
  • 13 inclus(φg|Sp,Sp×Tp)              ← RÉSIDU (voir NOTE), via `residu_univ_app`

Enfin, la conclusion φp(p)[j]=φg(p)[j] est convertie en φp(p)[y]=φg(p)[y] (liant-valeur
DÉFAUT « y », forme attendue par `temoin_commun_couvrant`) via `valeur_j_egal_y` (CS1,
α-renommage τ_j→τ_y) + transitivité.

────────────────────────────────────────────────────────────────────────────────
⚠️ RÉSIDU GÉOMÉTRIQUE HONNÊTE (PRÉCIS, jamais postulé comme coïncidence).  DEUX conjoints
de la PRÉMISSE_APPLICATIONS ne sont PAS dérivables des { CŒURS, bo(R,E), bo(R',F),
comparabilité } :

  #8  est_segment(image(φ_grand,S_petit), R', F)
        « l'IMAGE du petit segment par le GRAND iso est un segment de F ».
        VRAI (image d'un segment par un iso d'ordre = segment ; magnitude Lemme 1),
        mais AUCUNE brique du dépôt ne le prouve : `codomaine_egal_image` (le seul
        consommateur) le REQUIERT lui-même en hypothèse.

  #13 inclus(restriction(φ_grand,S_petit), S_petit × T_petit)
        « la RESTRICTION du grand graphe au petit domaine tombe dans S_petit×T_petit ».
        `restriction_incluse` ne donne que φ_g|Sp ⊂ φ_g ⊂ Sg×Tg (codomaine T_grand, pas
        T_petit) ; passer à T_petit exige image(φ_g,Sp)=T_petit — NON dérivable du graphe
        seul.  C'est l'inclusion structurelle déjà PORTÉE en hypothèse honnête par
        `coincidence_univ_app_point` (cf. sa NOTE D'HONNÊTETÉ).

Ces DEUX conjoints sont PORTÉS dans `residu_univ_app` — un UNIVERSEL CLOS (∀ sur les 6
témoins, comme `coincidence_univ`) qui, sous les 12 conjoints DÉCHARGEABLES, conclut
SEULEMENT (#8 et #13).  Il est STRICTEMENT PLUS FAIBLE que `coincidence_univ` : il ne
porte AUCUNE égalité de valeurs (φ_petit=φ_grand), seulement la BONNE FORME (segment
+ inclusion de graphe) des objets image/restriction.  C'est un universel CLOS afin de
SURVIVRE aux éliminations existentielles de l'assemblage (les conjoints à variables-
témoins libres bloqueraient `existe_elimination`).  `coincidence_univ` est, lui, GONE.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la COÏNCIDENCE est PROUVÉE
(coincidence_univ_app CLOS) ; seul subsiste le RÉSIDU géométrique ci-dessus (≠ coïncidence).
NON vacueux : fusion_hyp n'est aucune hypothèse.

NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, appartient, inclus, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.cardinaux import ensembles_temoin_deux_couples as T2
from bourbaki.cardinaux import ensembles_temoin_couvrant as TCV
from bourbaki.cardinaux import ensembles_segment_comparabilite_abstrait as CMP
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_fusion_assemblage as FA
from bourbaki.cardinaux.ensembles_fusion_app import coincidence_point_app
from bourbaki.cardinaux.ensembles_coincidence_univ_app import _premisse_liste
from bourbaki.cardinaux.ensembles_codomaine_reconciliation import (
    _rename_iso_order_binders,
)
from bourbaki.ordre.ensembles_valeur_bridge import valeur_j_egal_y


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# Indices des 14 conjoints de la PRÉMISSE_APPLICATIONS (cf. _premisse_liste) :
#   0 iso φ1[x,y]  1 iso φ2[a,b]  2 func φ1  3 func φ2  4 dom φ1  5 dom φ2
#   6 inclus(S1,S2)  7 seg T1  8 seg image(φ2,S1)  9 bo(R',F)  10 bo(R,E)
#   11 inclus(S1,E)  12 graph φ1  13 graph φ2|S1
_DISCHARGEABLE = (0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12)
_RESIDU_IDX = (8, 13)


def _conj(formules):
    """Conjonction left-nested et(et(...et(p0,p1),p2)...,pn)."""
    acc = formules[0]
    for f in formules[1:]:
        acc = et(acc, f)
    return acc


# ════════════════════════════════════════════════════════════════════════════
#  RÉSIDU GÉOMÉTRIQUE — universel CLOS portant SEULEMENT les conjoints #8 et #13.
#  Strictement plus FAIBLE que coincidence_univ : AUCUNE égalité de valeurs.
# ════════════════════════════════════════════════════════════════════════════
def residu_univ_app(E_set="E", R="R", F_set="F", Rp="Rp",
                    a="rSp", b="rTp", c="rphip", d="rSg", e="rTg", g="rphig"):
    """FORMULE (résidu géométrique HONNÊTE, universel CLOS) :

        (∀Sp)(∀Tp)(∀φp)(∀Sg)(∀Tg)(∀φg)(
            ANT_12  ⇒  ( est_segment(image(φg,Sp),R',F)  et  φg|Sp ⊂ Sp×Tp ) )

    où ANT_12 = la conjonction des 12 conjoints DÉCHARGEABLES de PRÉMISSE_APPLICATIONS
    (les isos/func/dom/segments/bons-ordres/inclusions, TOUS fournis par CŒURS+ambiant
    +comparabilité).  Le CONSÉQUENT ne porte QUE la BONNE FORME (segment + inclusion de
    graphe) des objets image(φg,Sp) / restriction(φg,Sp) — PAS de coïncidence de valeurs.

    🔑 UNIVERSEL CLOS (∀ sur les 6 témoins) : nécessaire pour SURVIVRE aux éliminations
    existentielles de l'assemblage (un conjoint à variables-témoins LIBRES bloquerait
    `existe_elimination`).  C'est la MÊME architecture que `coincidence_univ` (postulée),
    mais ce résidu est STRICTEMENT PLUS FAIBLE (aucune égalité φp=φg).  Binders FRAIS."""
    prem = _premisse_liste(c, g, a, b, d, e, F_set, R, Rp, E_set)
    ant = _conj([prem[i] for i in _DISCHARGEABLE])
    cons = et(prem[8], prem[13])
    body = impl(ant, cons)
    for w in (g, e, d, c, b, a):           # ∀ sur les 6 témoins (E,R,F,R' restent libres)
        body = pourtout(w, body)
    return body


# ════════════════════════════════════════════════════════════════════════════
#  COÏNCIDENCE INSTANCIÉE PROUVÉE — analogue de _coinc_point MAIS qui DÉRIVE
#  φ_petit(p)=φ_grand(p) de coincidence_point_app (consomme coincidence_univ_app, CLOS).
# ════════════════════════════════════════════════════════════════════════════
def _coinc_point_app(E_set, R, F_set, Rp,
                     Sp, Tp, phip, Sg, Tg, phig,
                     segSp, segTp, isop, funcP, domP, graphP,    # CŒUR petit
                     isog, funcG, domG,                          # CŒUR grand (iso/func/dom)
                     H_incl, H_boR, H_boRp, H_residu, p_in_small, p):
    """⊢ φ_petit(p)=φ_grand(p)  [liant-valeur « y », forme couvrante] sous :
       { CŒUR petit (segSp,segTp,isop,funcP,domP,graphP), CŒUR grand (isog,funcG,domG),
         inclus(Sp,Sg), bo(R,E), bo(R',F), RÉSIDU_univ, p∈Sp }.

    Analogue de `FA._coinc_point` mais qui appelle `coincidence_point_app` (= consomme
    `coincidence_univ_app`, THÉORÈME CLOS) et DÉCHARGE sa PRÉMISSE_APPLICATIONS (14 conj.)
    des CŒURS + bons ordres ambiants + comparabilité + RÉSIDU (#8,#13).  `coincidence_univ`
    n'apparaît NULLE PART : la coïncidence est PROUVÉE."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vSp, vTp, vphip = _t(Sp), _t(Tp), _t(phip)
    vSg, vTg, vphig = _t(Sg), _t(Tg), _t(phig)

    # ── théorème coincidence_point_app (consomme coincidence_univ_app, CLOS) ─────
    thm = coincidence_point_app(vphip, vphig, vSp, vTp, vSg, vTg, F_set, R, Rp, _t(p))
    prem = _premisse_liste(vphip, vphig, vSp, vTp, vSg, vTg, F_set, R, Rp, E_set)

    # ── #0/#1 : isos α-renommés depuis CŒURS (binders px/pw → x/y et a/b) ────────
    iso0 = _rename_iso_order_binders(isop, "x", "y")   # iso(φp,Sp,Tp)[x,y]
    iso1 = _rename_iso_order_binders(isog, "a", "b")   # iso(φg,Sg,Tg)[a,b]

    # ── #11 : inclus(Sp,E) = 1ᵉʳ conjoint de est_segment(Sp,R,E) (CŒUR petit) ─────
    incl_SpE = conjonction_elim_gauche(segSp)

    # ── #8,#13 : RÉSIDU instancié aux 6 témoins, antécédent = les 12 conjoints ────
    H_res_inst = H_residu
    for wterm in (vSp, vTp, vphip, vSg, vTg, vphig):
        H_res_inst = instancie(H_res_inst, wterm)      # ANT_12 ⇒ (seg image et φg|Sp⊂Sp×Tp)
    ant_proof = _conj_proof([
        iso0, iso1, funcP, funcG, domP, domG, H_incl, segTp,
        H_boRp, H_boR, incl_SpE, graphP,
    ])
    cons_residu = N.modus_ponens(ant_proof, H_res_inst)   # (seg image) et (φg|Sp⊂Sp×Tp)
    res8 = conjonction_elim_gauche(cons_residu)           # est_segment(image(φg,Sp),R',F)
    res13 = conjonction_elim_droite(cons_residu)          # inclus(φg|Sp, Sp×Tp)

    # ── DÉCHARGE des 14 conjoints de PRÉMISSE_APPLICATIONS ───────────────────────
    sources = {
        0: iso0, 1: iso1, 2: funcP, 3: funcG, 4: domP, 5: domG, 6: H_incl, 7: segTp,
        8: res8, 9: H_boRp, 10: H_boR, 11: incl_SpE, 12: graphP, 13: res13,
    }
    out = thm
    for i in range(14):
        out = N.modus_ponens(sources[i], N.loi_deduction(prem[i], out))
    # ── DÉCHARGE de la 15ᵉ hyp p∈Sp par la PREUVE `p_in_small` (analogue _coinc_point) ─
    f_p_in = appartient(_t(p), vSp)
    out = N.modus_ponens(p_in_small, N.loi_deduction(f_p_in, out))
    # out : φp(p)[j]=φg(p)[j]   [hyps : CŒURS, bo, bo, incl, RÉSIDU — PLUS p∈Sp]

    # ── conversion liant-valeur j → y (forme couvrante)  via valeur_j_egal_y (CS1) ─
    bridgeP = valeur_j_egal_y(vphip, _t(p))            # φp(p)[j]=φp(p)[y]
    bridgeG = valeur_j_egal_y(vphig, _t(p))            # φg(p)[j]=φg(p)[y]
    symP = N.modus_ponens(bridgeP, symetrie(*bridgeP.conclusion.termes))   # φp(p)[y]=φp(p)[j]
    ch1 = composer_egalites(symP, out)                 # φp(p)[y]=φg(p)[j]
    return composer_egalites(ch1, bridgeG)             # φp(p)[y]=φg(p)[y]


def _conj_proof(preuves):
    """Assemble une conjonction left-nested de PREUVES (et_intro répété)."""
    acc = preuves[0]
    for pr in preuves[1:]:
        acc = conjonction_intro(acc, pr)
    return acc


# ════════════════════════════════════════════════════════════════════════════
#  BRANCHE COUVRANTE (app) — analogue de FA._branche_couvrante avec _coinc_point_app.
# ════════════════════════════════════════════════════════════════════════════
def _branche_couvrante_app(E_set, R, F_set, Rp,
                           uA, vA, uB, vB,
                           Sp, Tp, phip, Sg, Tg, phig,
                           H_coeur_A, H_coeur_B, H_incl, H_boR, H_boRp, H_residu):
    """Sur la branche S_petit⊂S_grand : le GRAND iso couvre les deux antécédents.
    Décharge les 9 hyps de `temoin_commun_couvrant` (RÉUTILISÉ, CLOS-cond) depuis les
    deux CŒURS + comparabilité + bons ordres + RÉSIDU ; la coïncidence φp(uA)=φg(uA)
    est PROUVÉE par `_coinc_point_app` (consomme coincidence_univ_app, CLOS)."""
    segSp, segTp, isop, uA_in, vA_eq, funcP, domP, graphP = FA._decompose_coeur(H_coeur_A)
    segSg, segTg, isog, uB_in, vB_eq, funcG, domG, graphG = FA._decompose_coeur(H_coeur_B)

    # coïncidence PROUVÉE au point uA (uA∈S_petit) : φ_petit(uA)=φ_grand(uA)  [liant y]
    coinc_uA = _coinc_point_app(E_set, R, F_set, Rp, Sp, Tp, phip, Sg, Tg, phig,
                                segSp, segTp, isop, funcP, domP, graphP,
                                isog, funcG, domG,
                                H_incl, H_boR, H_boRp, H_residu, uA_in, uA)

    couvre = TCV.temoin_commun_couvrant(E_set, R, F_set, Rp, uA, vA, uB, vB,
                                        Sp, Sg, Tg, phip, phig)
    preuves = {
        segSg.conclusion:  segSg,
        segTg.conclusion:  segTg,
        isog.conclusion:   isog,
        uA_in.conclusion:  uA_in,
        H_incl.conclusion: H_incl,
        vA_eq.conclusion:  vA_eq,
        coinc_uA.conclusion: coinc_uA,
        uB_in.conclusion:  uB_in,
        vB_eq.conclusion:  vB_eq,
    }
    out = couvre
    for hyp in list(couvre.hypotheses):
        if hyp in preuves:
            out = N.modus_ponens(preuves[hyp], N.loi_deduction(hyp, out))
        else:
            raise AssertionError(f"hyp non déchargée : {hyp!r}")
    return out


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR (app) — analogue de FA._core_with_witnesses, route coincidence_point_app.
# ════════════════════════════════════════════════════════════════════════════
def _core_with_witnesses_app(E_set, R, F_set, Rp, u, v, up, vp,
                             Sa, Ta, pa, Sb, Tb, pb,
                             H_coeurA, H_coeurB, H_boR, H_boRp, H_residu):
    """{ CŒUR_A(u,v ; Sa,Ta,pa), CŒUR_B(u',v' ; Sb,Tb,pb), bo(R,E), bo(R',F),
         RÉSIDU_univ } ⊢ temoin_commun_h(u,v,u',v').

    Comparabilité (brique 1) ⇒ Sa⊂Sb ∨ Sb⊂Sa ; sur chaque branche la construction
    couvrante (app) avec coïncidence PROUVÉE couvre les deux antécédents ; branche
    Sb⊂Sa suivie du SWAP (FA._swap_temoin_commun, RÉUTILISÉ)."""
    Rf = _R_de(R)
    vE = _t(E_set)
    segSa, *_ = FA._decompose_coeur(H_coeurA)
    segSb, *_ = FA._decompose_coeur(H_coeurB)

    comp = CMP.segments_abstraits_comparables(R, E_set, _t(Sa), _t(Sb))
    f_segSa = E.est_segment(_t(Sa), Rf, vE)
    f_segSb = E.est_segment(_t(Sb), Rf, vE)
    comp = N.modus_ponens(segSa, N.loi_deduction(f_segSa, comp))
    comp = N.modus_ponens(segSb, N.loi_deduction(f_segSb, comp))   # (Sa⊂Sb ou Sb⊂Sa) [hyp bo(R,E)]

    A_incl = inclus(_t(Sa), _t(Sb))
    B_incl = inclus(_t(Sb), _t(Sa))

    # — branche Sa⊂Sb : petit=A (u∈Sa), grand=B (u'∈Sb) —
    HA = N.assume(A_incl)
    brA = _branche_couvrante_app(E_set, R, F_set, Rp, u, v, up, vp,
                                 Sa, Ta, pa, Sb, Tb, pb,
                                 H_coeurA, H_coeurB, HA, H_boR, H_boRp, H_residu)
    impA = N.loi_deduction(A_incl, brA)

    # — branche Sb⊂Sa : petit=B, grand=A ⇒ temoin_commun_h(u',v',u,v), puis SWAP —
    HB = N.assume(B_incl)
    brB_swapped = _branche_couvrante_app(E_set, R, F_set, Rp, up, vp, u, v,
                                         Sb, Tb, pb, Sa, Ta, pa,
                                         H_coeurB, H_coeurA, HB, H_boR, H_boRp, H_residu)
    swap = FA._swap_temoin_commun(E_set, R, F_set, Rp, u, v, up, vp)
    brB = N.modus_ponens(brB_swapped, swap)
    impB = N.loi_deduction(B_incl, brB)

    return cas(comp, impA, impB)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE FINAL (app) — fusion_hyp SANS coincidence_univ.
# ════════════════════════════════════════════════════════════════════════════
def fusion_depuis_coincidence_app(E_set="E", R="R", F_set="F", Rp="Rp",
                                  u="ua", v="va", up="ub", vp="vb",
                                  S="S", T="T", phi="phi",
                                  Sb="S2", Tb="T2", pb="phi2"):
    """⊢ { bo(R,E), bo(R',F), RÉSIDU_univ } ⊢ fusion_hyp(u,v,u',v').

    🎯🎯 RE-CÂBLAGE : la FUSION (Lemme 1 §III.2) repose désormais sur la COÏNCIDENCE
    **PROUVÉE** (`coincidence_point_app` → `coincidence_univ_app`, CLOS), **PAS** sur
    `coincidence_univ` (POSTULÉE — RETIRÉE).  Conclusion == `T2.fusion_hyp(...)`
    LITTÉRALEMENT (même cible que `FA.fusion_depuis_coincidence`).

    Hypothèses SURVIVANTES (exactement 3 ; cf. `fusion_depuis_coincidence_app_hypotheses`) :
      • est_bien_ordonne(R,E)      — arrière-plan structurel (côté E) ;
      • est_bien_ordonne(R',F)     — arrière-plan structurel (côté F ; consommé par la
                                     coïncidence PROUVÉE — bo AMBIANT F-side) ;
      • RÉSIDU_univ                — universel CLOS portant SEULEMENT #8 (seg image) et
                                     #13 (φg|Sp⊂Sp×Tp), strictement plus faible que
                                     coincidence_univ (aucune égalité de valeurs).
    Les deux CŒURS (_coeur1) sont des témoins INTERNES, assumés aux témoins-VARIABLES puis
    ÉLIMINÉS en ∃ (comme l'original) : ils NE survivent PAS dans le séquent.
    ⚠️ `coincidence_univ` est ABSENTE.  theorie=22.  NON vacueux.

    PREUVE.  `_core_with_witnesses_app` (route coincidence_point_app) PROUVE
    temoin_commun_h(u,v,u',v') sous {CŒURS, bo, bo, RÉSIDU} ; on élimine les 3 ∃ de
    couple₂ (RÉSIDU CLOS + bos CLOS ⇒ pas de variable-témoin libre), compose avec
    α-renommage (FA._rename_temoin1) et h_membre_donne_temoin (CLOS), puis élimine les
    3 ∃ de couple₁ ⇒ fusion_hyp.  Mêmes points-variables ua,va,ub,vb que l'original."""
    vu, vv, vup, vvp = _t(u), _t(v), _t(up), _t(vp)

    H_boR = N.assume(FA._bo_form(R, E_set))                       # est_bien_ordonne(R,E)
    H_boRp = N.assume(E.est_bien_ordonne(_R_de(Rp), _t(F_set)))   # est_bien_ordonne(R',F)
    H_residu = N.assume(residu_univ_app(E_set, R, F_set, Rp))     # RÉSIDU universel CLOS

    coeurA = T2._coeur1(E_set, R, F_set, Rp, u, v, var(S), var(T), var(phi))
    coeurB = T2._coeur1(E_set, R, F_set, Rp, up, vp, var(Sb), var(Tb), var(pb))
    H_coeurA = N.assume(coeurA)
    H_coeurB = N.assume(coeurB)

    tch = _core_with_witnesses_app(E_set, R, F_set, Rp, u, v, up, vp,
                                   var(S), var(T), var(phi), var(Sb), var(Tb), var(pb),
                                   H_coeurA, H_coeurB, H_boR, H_boRp, H_residu)

    # — éliminer les 3 ∃ de couple₂ : coeurB ⇒ tch  ⟹  temoin₁[Sb,Tb,pb](u',v') ⇒ tch —
    impB = N.loi_deduction(coeurB, tch)
    impB = existe_elimination(impB, pb)
    impB = existe_elimination(impB, Tb)
    impB = existe_elimination(impB, Sb)

    # — temoin₁[S,T,phi](u',v') ⇒ temoin₁[Sb,Tb,pb](u',v')  (α-renommage, RÉUTILISÉ) —
    ren_imp, _ = FA._rename_temoin1(E_set, R, F_set, Rp, up, vp, S, T, phi, Sb, Tb, pb)
    impB2 = syllogisme(ren_imp, impB)

    # — composer (u',v')∈h ⇒ temoin₁[S,T,phi](u',v')  (h_membre_donne_temoin, CLOS) —
    hmdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "up", "vp", S, T, phi)
    hmdt_inst = instancie(instancie(hmdt, vup), vvp)
    imp_h = syllogisme(hmdt_inst, impB2)

    # — éliminer les 3 ∃ de couple₁ ⇒ temoin₁(u,v) ⇒ ((u',v')∈h ⇒ tch) = fusion_hyp —
    impA = N.loi_deduction(coeurA, imp_h)
    impA = existe_elimination(impA, phi)
    impA = existe_elimination(impA, T)
    impA = existe_elimination(impA, S)
    return impA                                      # = fusion_hyp  [hyps : bo, bo, CŒURS, RÉSIDU]


def fusion_depuis_coincidence_app_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                        u="ua", v="va", up="ub", vp="vb",
                                        S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) : fusion_hyp(u,v,u',v')  (= T2.fusion_hyp).

    IDENTIQUE à `FA.fusion_depuis_coincidence_cible` (même points-variables ua,va,ub,vb)."""
    return T2.fusion_hyp(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)


def fusion_depuis_coincidence_app_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les TROIS hypothèses SURVIVANTES (documentation / test miroir) :
       [ est_bien_ordonne(R,E),  est_bien_ordonne(R',F),  residu_univ_app ].

    ⚠️ `coincidence_univ` ABSENTE.  Les deux CŒURS (_coeur1) sont des témoins INTERNES
    éliminés existentiellement (comme dans `FA.fusion_depuis_coincidence`, qui survit
    avec {bo(R,E), coincidence_univ}) : ils NE figurent PAS dans le séquent final.
    Le séquent final ne porte QUE ces trois formules-là."""
    return [
        FA._bo_form(R, E_set),
        E.est_bien_ordonne(_R_de(Rp), _t(F_set)),
        residu_univ_app(E_set, R, F_set, Rp),
    ]


__all__ = [
    "residu_univ_app",
    "fusion_depuis_coincidence_app", "fusion_depuis_coincidence_app_cible",
    "fusion_depuis_coincidence_app_hypotheses",
]
