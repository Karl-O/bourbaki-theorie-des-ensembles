"""§III.2 — Théorème 3 (TRICHOTOMIE) : ASSEMBLAGE de fusion_hyp MODULO coïncidence.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  RÉDUIRE l'hypothèse de FUSION du Lemme 1 §III.2 (`ensembles_temoin_deux_couples.
fusion_hyp`) à la SEULE COÏNCIDENCE des isos sur le chevauchement.  La FUSION

    fusion_hyp :=  temoin₁(u,v)  ⇒  ( (u',v')∈h  ⇒  temoin_commun_h(u,v,u',v') )

(« connaissant l'iso témoin du PREMIER couple et le second couple (u',v')∈h, UN SEUL
iso de segments couvre les deux antécédents ») était jusqu'ici POSÉE en hypothèse
opaque.  Ce module la DÉRIVE des deux TÉMOINS de segments + de la comparabilité des
segments d'un bon ordre + de la construction couvrante, ne laissant en hypothèse QUE :

  • `est_bien_ordonne(R,E)`  — l'ARRIÈRE-PLAN structurel (R bien-ordonne E, donnée du
    Théorème 3) ;
  • `coincidence_univ`        — la SEULE COÏNCIDENCE GÉOMÉTRIQUE (Lemme 1 §III.2,
    universalisée) : deux isos de segments EMBOÎTÉS coïncident sur le plus petit.

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (salvage fort, honnête, theorie=22, rien postulé) :

  ✅ `fusion_depuis_coincidence(...)` :
        { est_bien_ordonne(R,E),  coincidence_univ }  ⊢  fusion_hyp(u,v,u',v').
     i.e. CONCLUSION == `ensembles_temoin_deux_couples.fusion_hyp(...)` LITTÉRALEMENT,
     conditionnée aux SEULES deux hypothèses ci-dessus.

  Mécanique (RÉUTILISE, ne reprouve pas) :
    1. EXTRACTION des DEUX témoins de segments :  temoin₁(u,v) [antécédent de fusion_hyp]
       et temoin₁(u',v') [via `h_membre_donne_temoin`, CLOS, sur (u',v')∈h] ;
       chacun donne, par élimination existentielle, un iso de segments
       (S₁,T₁,φ₁) resp. (S₂,T₂,φ₂) avec u∈S₁, v=φ₁(u) resp. u'∈S₂, v'=φ₂(u').
    2. COMPARABILITÉ (brique 1, `segments_abstraits_comparables`, CLOS-cond) :
       S₁⊂S₂  ou  S₂⊂S₁  (segments d'un MÊME bon ordre E ⇒ emboîtés).
    3. CONSTRUCTION COUVRANTE (brique 2, `temoin_commun_couvrant`) : sur chaque branche
       le PLUS GRAND iso couvre les deux antécédents — d'où temoin_commun_h(u,v,u',v').
       La SEULE chose géométrique consommée à cette étape = la COÏNCIDENCE φ_petit=φ_grand
       sur le petit segment, fournie par `coincidence_univ` (Lemme 1 reporté).
    4. Branche S₂⊂S₁ symétrique (rôles des deux couples échangés) + ré-ordonnancement
       des conjoints de temoin_commun_h (lemme de SWAP des antécédents).
    5. Élimination des 6 existentiels (S₁,T₁,φ₁,S₂,T₂,φ₂ NON libres dans la conclusion)
       puis recomposition de fusion_hyp.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout vient des bricks CLOS et de
deux hypothèses EXPLICITES.  NON vacueux : fusion_hyp n'est aucune des deux hypothèses.

────────────────────────────────────────────────────────────────────────────────
⚠️ REPORTÉ précisément (JAMAIS postulé) : la PREUVE inconditionnelle de
`coincidence_univ` (= deux isos de segments emboîtés coïncident sur le chevauchement,
unicité de l'iso de segments d'un bon ordre, Lemme 1 §III.2, magnitude Cantor–Bernstein).
C'est désormais la SEULE pièce manquante de fusion_hyp (avec l'arrière-plan structurel
est_bien_ordonne(R,E)).  Déchargeable des bricks coincidence_sur_chevauchement /
auto_iso_est_identite (résidu = pont représentationnel liant-valeur).

NE MODIFIE AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, tau, egal, et, impl, appartient, inclus, existe, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    monotonie_existe, existe_elimination,
)
from bourbaki.cardinaux import ensembles_temoin_deux_couples as T2
from bourbaki.cardinaux import ensembles_temoin_couvrant as TCV
from bourbaki.cardinaux import ensembles_segment_comparabilite_abstrait as CMP
from bourbaki.cardinaux import ensembles_trichotomie_coherences as COH
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_ISO_X, _ISO_Y = "px", "pw"          # binders d'iso canoniques (anti-capture-y)


def _iso(phi, S, T, Rf, Rpf):
    return V.est_isomorphisme_ordre(_t(phi), _t(S), _t(T), Rf, Rpf, _ISO_X, _ISO_Y)


# ════════════════════════════════════════════════════════════════════════════
#  COÏNCIDENCE UNIVERSELLE (Lemme 1 §III.2, universalisée) — la SEULE hypothèse
#  géométrique reportée : deux isos de segments EMBOÎTÉS coïncident sur le petit.
# ════════════════════════════════════════════════════════════════════════════
def coincidence_univ(E_set="E", R="R", F_set="F", Rp="Rp",
                     a="qSa", b="qTa", c="qpa", d="qSb", e="qTb", g="qpb", w="qw"):
    """FORMULE (hypothèse géométrique EXPLICITE = COÏNCIDENCE de Lemme 1 §III.2) :

        (∀S₁)(∀T₁)(∀φ₁)(∀S₂)(∀T₂)(∀φ₂)(
            ( est_segment(S₁,R,E) et est_segment(T₁,Rp,F) et iso(φ₁,S₁,T₁)
              et est_segment(S₂,R,E) et est_segment(T₂,Rp,F) et iso(φ₂,S₂,T₂)
              et S₁⊂S₂ )
            ⇒ (∀w)( w∈S₁ ⇒ φ₁(w)=φ₂(w) ) )

    « deux isos d'ordre de SEGMENTS EMBOÎTÉS (S₁⊂S₂) coïncident sur le plus petit S₁ ».
    C'est EXACTEMENT la coïncidence sur le chevauchement du Lemme 1 §III.2 (unicité de
    l'iso de segments d'un bon ordre), universalisée.  VRAIE, non triviale, DIFFÉRENTE
    de fusion_hyp / temoin_commun_h (elle porte une ÉGALITÉ de valeurs, non un témoin).
    Posée EXPLICITE, jamais comme théorème.  Les binders sont FRAIS (qSa…qw) pour ne
    capturer aucune variable libre des assemblages."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    vS1, vT1, vphi1 = var(a), var(b), var(c)
    vS2, vT2, vphi2 = var(d), var(e), var(g)
    vw = var(w)
    premisse = et(et(et(et(et(et(
        E.est_segment(vS1, Rf, vE),
        E.est_segment(vT1, Rpf, vF)),
        _iso(vphi1, vS1, vT1, Rf, Rpf)),
        E.est_segment(vS2, Rf, vE)),
        E.est_segment(vT2, Rpf, vF)),
        _iso(vphi2, vS2, vT2, Rf, Rpf)),
        inclus(vS1, vS2))
    conclusion = pourtout(w, impl(appartient(vw, vS1),
                                  egal(E.valeur(vphi1, vw), E.valeur(vphi2, vw))))
    return pourtout(a, pourtout(b, pourtout(c, pourtout(d, pourtout(e, pourtout(g,
        impl(premisse, conclusion)))))))


# ════════════════════════════════════════════════════════════════════════════
#  Décomposition des deux CŒURS (= corps de _temoin1_ex) en leurs 5 conjoints.
#    coeur₁ = ((((seg S, seg T), iso(φ,S,T)), u∈S), v=φ(u))   (forme de _coeur1)
# ════════════════════════════════════════════════════════════════════════════
def _decompose_coeur(Hc):
    """De ⊢ coeur (= _coeur1 / _temoin1_ex body, STRENGTHENED 8 conjoints) extrait
    (segS, segT, iso, in, val, func, dom, graph).

    ⚠️ ARCHITECTURE func/dom : le cœur porte maintenant 8 conjoints —
        et(et(et(coeur5, func), dom), graphe).
    On PÈLE d'abord les 3 conjoints externes (graphe, dom, func) puis on applique la
    logique d'origine sur coeur5.  On APPEND (func, dom, graph) au tuple retourné
    (les appelants qui ne s'en servent pas ignorent les extras)."""
    graph = conjonction_elim_droite(Hc)             # φ⊂S×T
    r = conjonction_elim_gauche(Hc)                 # et(et(coeur5, func), dom)
    dom = conjonction_elim_droite(r)                # dom(φ)=S
    r = conjonction_elim_gauche(r)                  # et(coeur5, func)
    func = conjonction_elim_droite(r)               # est_fonctionnel(φ)
    Hc5 = conjonction_elim_gauche(r)                # coeur5 (5 conjoints originaux)
    val = conjonction_elim_droite(Hc5)              # v=φ(u)
    r1 = conjonction_elim_gauche(Hc5)               # (((seg,seg),iso),u∈S)
    inn = conjonction_elim_droite(r1)               # u∈S
    r2 = conjonction_elim_gauche(r1)                # ((seg,seg),iso)
    iso = conjonction_elim_droite(r2)               # iso(φ,S,T)
    r3 = conjonction_elim_gauche(r2)                # (seg S, seg T)
    segS = conjonction_elim_gauche(r3)              # seg S
    segT = conjonction_elim_droite(r3)              # seg T
    return segS, segT, iso, inn, val, func, dom, graph


# ════════════════════════════════════════════════════════════════════════════
#  COÏNCIDENCE INSTANCIÉE — de coincidence_univ + les deux cœurs + S_petit⊂S_grand,
#  produire  φ_petit(p)=φ_grand(p)  pour un point p∈S_petit.
# ════════════════════════════════════════════════════════════════════════════
def _coinc_point(Hcoinc, Sp, Tp, phip, Sg, Tg, phig,
                 segSp, segTp, isop, segSg, segTg, isog, Hincl, p_in_small, p):
    """De coincidence_univ (Hcoinc) instanciée aux 6 témoins (S₁,T₁,φ₁ petit ;
    S₂,T₂,φ₂ grand) + leurs segments/isos + (S_petit⊂S_grand) + (p∈S_petit) déduit
    φ_petit(p)=φ_grand(p).

    Sp,Tp,phip = TERMES du PETIT iso ; Sg,Tg,phig = du GRAND ;
    segSp,segTp,isop / segSg,segTg,isog = leurs PREUVES (conjoints des cœurs) ;
    Hincl : S_petit⊂S_grand ; p_in_small : p∈S_petit ; p : le point (terme)."""
    inst = instancie(instancie(instancie(instancie(instancie(instancie(
        Hcoinc, _t(Sp)), _t(Tp)), _t(phip)), _t(Sg)), _t(Tg)), _t(phig))
    # antécédent : conjonction des 6 conjoints + inclusion (forme EXACTE de la prémisse)
    prem_proof = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(conjonction_intro(segSp, segTp), isop), segSg), segTg), isog), Hincl)
    forall_w = N.modus_ponens(prem_proof, inst)     # (∀w)(w∈S_petit ⇒ φ_p(w)=φ_g(w))
    imp_p = instancie(forall_w, _t(p))              # p∈S_petit ⇒ φ_p(p)=φ_g(p)
    return N.modus_ponens(p_in_small, imp_p)        # φ_p(p)=φ_g(p)


# ════════════════════════════════════════════════════════════════════════════
#  Décharge des 9 hypothèses de `temoin_commun_couvrant` (PETIT=couple A, GRAND=couple B).
#  Produit temoin_commun_h(uA,vA,uB,vB) sous les hyps {coeurA, coeurB, incl, coincidence}.
# ════════════════════════════════════════════════════════════════════════════
def _branche_couvrante(E_set, R, F_set, Rp,
                       uA, vA, uB, vB,                 # uA dans le PETIT, uB dans le GRAND
                       Sp, Tp, phip, Sg, Tg, phig,    # TERMES : petit (A) / grand (B)
                       H_coeur_A, H_coeur_B, H_incl, H_coinc):
    """Sur la branche S_petit⊂S_grand, le GRAND iso (φ_grand:S_grand≅T_grand) couvre les
    deux antécédents.  Décharge les 9 hyps de temoin_commun_couvrant depuis :
      • coeur_A (petit, uA∈S_petit, vA=φ_petit(uA)),
      • coeur_B (grand, uB∈S_grand, vB=φ_grand(uB)),
      • H_incl : S_petit⊂S_grand,
      • H_coinc : coincidence_univ.
    Conclusion : temoin_commun_h(uA,vA,uB,vB) (binders S,T,phi)."""
    # conjoints des cœurs (8-uplet : on ignore func/dom/graphe ici)
    segSp, segTp, isop, uA_in, vA_eq, *_ = _decompose_coeur(H_coeur_A)   # petit
    segSg, segTg, isog, uB_in, vB_eq, *_ = _decompose_coeur(H_coeur_B)   # grand
    # coïncidence au point uA (uA∈S_petit) : φ_petit(uA)=φ_grand(uA)
    coinc_uA = _coinc_point(H_coinc, Sp, Tp, phip, Sg, Tg, phig,
                            segSp, segTp, isop, segSg, segTg, isog, H_incl, uA_in, uA)
    # brique 2 : temoin_commun_couvrant (PETIT=Sp/φ_petit, GRAND=Sg/Tg/φ_grand)
    couvre = TCV.temoin_commun_couvrant(E_set, R, F_set, Rp, uA, vA, uB, vB,
                                        Sp, Sg, Tg, phip, phig)
    # ses 9 hyps EXACTES (cf. signature) à décharger :
    #   seg Sg, seg Tg, iso(φg,Sg,Tg), uA∈Sp, Sp⊂Sg, vA=φp(uA), φp(uA)=φg(uA),
    #   uB∈Sg, vB=φg(uB)
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
#  SWAP des antécédents — temoin_commun_h(u',v',u,v) ⇒ temoin_commun_h(u,v,u',v').
#  Même corps existentiel, conjoints ré-ordonnés (u∈S↔u'∈S, v=φ(u)↔v'=φ(u')).
# ════════════════════════════════════════════════════════════════════════════
def _swap_temoin_commun(E_set, R, F_set, Rp, u, v, up, vp, S="S", T="T", phi="phi"):
    """⊢ temoin_commun_h(u',v',u,v) ⇒ temoin_commun_h(u,v,u',v').  INCONDITIONNEL.

    Les deux formules ont le MÊME corps existentiel (∃S,T,φ) à conjoints PERMUTÉS
    (couverture symétrique des deux antécédents).  On prouve l'implication des CŒURS
    par ré-assemblage des 6 conjoints, puis on remonte les 3 ∃ (monotonie_existe)."""
    coeur_src = COH._temoin_commun_coeur(E_set, R, F_set, Rp, up, vp, u, v, S, T, phi)
    Hc = N.assume(coeur_src)
    # extraire les 7 conjoints de coeur(up,vp,u,v) :
    #  ((((((seg S, seg T), iso), up∈S), u∈S), vp=φ(up)), v=φ(u))
    c_vfu = conjonction_elim_droite(Hc)             # v=φ(u)
    r1 = conjonction_elim_gauche(Hc)                # (((((segS,segT),iso),up∈S),u∈S),vp=φ(up))
    c_vpfup = conjonction_elim_droite(r1)           # vp=φ(up)
    r2 = conjonction_elim_gauche(r1)                # ((((segS,segT),iso),up∈S),u∈S)
    c_uin = conjonction_elim_droite(r2)             # u∈S
    r3 = conjonction_elim_gauche(r2)                # (((segS,segT),iso),up∈S)
    c_upin = conjonction_elim_droite(r3)            # up∈S
    r4 = conjonction_elim_gauche(r3)                # ((segS,segT),iso)
    c_iso = conjonction_elim_droite(r4)             # iso(φ,S,T)
    r5 = conjonction_elim_gauche(r4)                # (segS,segT)
    c_segS = conjonction_elim_gauche(r5)            # seg S
    c_segT = conjonction_elim_droite(r5)            # seg T
    # ré-assembler coeur(u,v,up,vp) :
    #  ((((((segS,segT),iso),u∈S),up∈S),v=φ(u)),vp=φ(up))
    tgt = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(conjonction_intro(c_segS, c_segT), c_iso), c_uin), c_upin),
        c_vfu), c_vpfup)
    coeur_tgt = COH._temoin_commun_coeur(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)
    assert tgt.conclusion == coeur_tgt, "swap coeur mismatch"
    imp = N.loi_deduction(coeur_src, tgt)           # coeur(up,vp,u,v) ⇒ coeur(u,v,up,vp)
    imp = monotonie_existe(imp, phi)
    imp = monotonie_existe(imp, T)
    imp = monotonie_existe(imp, S)                  # temoin_commun_h(up,vp,u,v) ⇒ temoin_commun_h(u,v,up,vp)
    return imp


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR — depuis les DEUX cœurs (witnesses libres S,T,φ et S2,T2,φ2), l'arrière-plan
#  est_bien_ordonne(R,E) et la coïncidence, PROUVER temoin_commun_h(u,v,u',v').
# ════════════════════════════════════════════════════════════════════════════
def _core_with_witnesses(E_set, R, F_set, Rp, u, v, up, vp,
                         Sa, Ta, pa, Sb, Tb, pb,
                         H_coeurA, H_coeurB, H_bo, H_coinc):
    """{ coeurA(u,v ; Sa,Ta,pa), coeurB(u',v' ; Sb,Tb,pb),
         est_bien_ordonne(R,E),  coincidence_univ }
            ⊢ temoin_commun_h(u,v,u',v').

    Comparabilité (brique 1) des segments Sa,Sb (du MÊME bon ordre E) ⇒ Sa⊂Sb ou Sb⊂Sa ;
    sur chaque branche la construction couvrante (brique 2) avec le PLUS GRAND iso couvre
    les deux antécédents ; branche Sb⊂Sa suivie du SWAP des antécédents."""
    Rf = _R_de(R)
    vE = _t(E_set)
    segSa, *_ = _decompose_coeur(H_coeurA)
    segSb, *_ = _decompose_coeur(H_coeurB)

    # — comparabilité Sa,Sb (brique 1) : décharger les 2 hyps de segment depuis les cœurs —
    comp = CMP.segments_abstraits_comparables(R, E_set, _t(Sa), _t(Sb))
    # ses 3 hyps : est_bien_ordonne(R,E), est_segment(Sa), est_segment(Sb)
    f_segSa = E.est_segment(_t(Sa), Rf, vE)
    f_segSb = E.est_segment(_t(Sb), Rf, vE)
    comp = N.modus_ponens(segSa, N.loi_deduction(f_segSa, comp))
    comp = N.modus_ponens(segSb, N.loi_deduction(f_segSb, comp))
    # comp : (Sa⊂Sb ou Sb⊂Sa)  sous { est_bien_ordonne(R,E) }  (à décharger plus bas)

    A_incl = inclus(_t(Sa), _t(Sb))                 # Sa⊂Sb
    B_incl = inclus(_t(Sb), _t(Sa))                 # Sb⊂Sa

    # — branche Sa⊂Sb : petit=A (u∈Sa), grand=B (u'∈Sb) ⇒ temoin_commun_h(u,v,u',v') —
    HA = N.assume(A_incl)
    brA = _branche_couvrante(E_set, R, F_set, Rp, u, v, up, vp,
                             Sa, Ta, pa, Sb, Tb, pb, H_coeurA, H_coeurB, HA, H_coinc)
    impA = N.loi_deduction(A_incl, brA)             # Sa⊂Sb ⇒ goal

    # — branche Sb⊂Sa : petit=B (u'∈Sb), grand=A (u∈Sa) ⇒ temoin_commun_h(u',v',u,v),
    #   puis SWAP ⇒ temoin_commun_h(u,v,u',v') —
    HB = N.assume(B_incl)
    brB_swapped = _branche_couvrante(E_set, R, F_set, Rp, up, vp, u, v,
                                     Sb, Tb, pb, Sa, Ta, pa, H_coeurB, H_coeurA, HB, H_coinc)
    swap = _swap_temoin_commun(E_set, R, F_set, Rp, u, v, up, vp)
    brB = N.modus_ponens(brB_swapped, swap)         # temoin_commun_h(u,v,u',v')
    impB = N.loi_deduction(B_incl, brB)             # Sb⊂Sa ⇒ goal

    out = cas(comp, impA, impB)                     # goal  (comp décharge le ∨)
    return out


# ════════════════════════════════════════════════════════════════════════════
#  α-RENOMMAGE du témoin de segment de couple₂.  temoin₁(u',v') a TOUJOURS les binders
#  S,T,phi (l'axiome de h les fixe).  On le renomme en VARIABLES FRAÎCHES Sb,Tb,pb pour
#  ne PAS collisionner avec les witnesses S,T,phi de couple₁ — par CŒUR-variable + S5
#  (clean, sans explosion ni gensym parasite, cf. _rename_temoin1).
# ════════════════════════════════════════════════════════════════════════════
def _cons(thm_imp):
    """Le CONSÉQUENT C de ⊢ (A⇒C)  (sans hypothèse de forme)."""
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    return antecedent_consequent(thm_imp.conclusion)[1]


def _peel3(H_temoin, S, T, phi):
    """De H_temoin ⊢ (∃S)(∃T)(∃φ)coeur, extrait (wS, wT, wφ, ⊢coeur(wS,wT,wφ)) par
    `existe_temoin` (réciproque de S5 au témoin canonique τ — robuste, pas d'égalité).
    wS,wT,wφ sont des TERMES-τ concrets."""
    bodyS = H_temoin.conclusion.sous[0]              # corps de (∃S) : (∃T)(∃φ)coeur
    wS = tau(S, bodyS)
    exTphi = N.modus_ponens(H_temoin, N.existe_temoin(bodyS, S))   # (∃T)(∃φ)coeur(wS,·)
    bodyT = exTphi.conclusion.sous[0]
    wT = tau(T, bodyT)
    exphi = N.modus_ponens(exTphi, N.existe_temoin(bodyT, T))      # (∃φ)coeur(wS,wT,·)
    bodyphi = exphi.conclusion.sous[0]
    wphi = tau(phi, bodyphi)
    coeur = N.modus_ponens(exphi, N.existe_temoin(bodyphi, phi))   # coeur(wS,wT,wφ)
    return wS, wT, wphi, coeur


def _rename_temoin1(E_set, R, F_set, Rp, up, vp, S, T, phi, Sb, Tb, pb):
    """⊢ temoin₁[S,T,phi](u',v') ⇒ temoin₁[Sb,Tb,pb](u',v')  (CLEAN, INCONDITIONNEL).

    α-renommage des binders S,T,phi → Sb,Tb,pb.  On assume le CŒUR aux VARIABLES S,T,phi
    (subst sans explosion ni capture, contrairement aux τ-témoins), on le ré-introduit
    dans le corps CLEAN coeur(Sb,Tb,pb) par trois S5 (témoins = var(S),var(T),var(phi)),
    puis on élimine les 3 ∃ (S,T,phi NON libres dans temoin₁[Sb,Tb,pb]).  Forme MANUELLE
    propre (aucun gensym @).  Retourne (implication, cible temoin₁[Sb,Tb,pb])."""
    coeur = T2._coeur1(E_set, R, F_set, Rp, up, vp, var(S), var(T), var(phi))   # coeur(S,T,phi)
    H_coeur = N.assume(coeur)
    # ré-introduire dans le corps CLEAN coeur(Sb,Tb,pb) par S5 (témoins = variables S,T,phi)
    coeur_pb = T2._coeur1(E_set, R, F_set, Rp, up, vp, var(S), var(T), var(pb))         # coeur(S,T,pb)
    ex_pb = N.modus_ponens(H_coeur, N.s5(coeur_pb, var(phi), pb))        # (∃pb)coeur(S,T,pb)
    coeur_Tb = existe(pb, T2._coeur1(E_set, R, F_set, Rp, up, vp, var(S), var(Tb), var(pb)))
    ex_Tb = N.modus_ponens(ex_pb, N.s5(coeur_Tb, var(T), Tb))           # (∃Tb)(∃pb)coeur(S,Tb,pb)
    coeur_Sb = existe(Tb, existe(pb, T2._coeur1(E_set, R, F_set, Rp, up, vp,
                                                var(Sb), var(Tb), var(pb))))
    ex_Sb = N.modus_ponens(ex_Tb, N.s5(coeur_Sb, var(S), Sb))          # (∃Sb)(∃Tb)(∃pb)coeur(Sb,Tb,pb)
    imp_coeur = N.loi_deduction(coeur, ex_Sb)                          # coeur(S,T,phi) ⇒ temoin₁[Sb,Tb,pb]
    # éliminer les 3 ∃ de la source : temoin₁[S,T,phi] ⇒ temoin₁[Sb,Tb,pb]
    imp = existe_elimination(imp_coeur, phi)
    imp = existe_elimination(imp, T)
    imp = existe_elimination(imp, S)
    return imp, _cons(imp)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 ASSEMBLAGE FINAL — fusion_hyp DÉRIVÉE de est_bien_ordonne(R,E) + coincidence_univ.
# ════════════════════════════════════════════════════════════════════════════
def fusion_depuis_coincidence(E_set="E", R="R", F_set="F", Rp="Rp",
                              u="ua", v="va", up="ub", vp="vb",
                              S="S", T="T", phi="phi",
                              Sb="S2", Tb="T2", pb="phi2"):
    """⊢ { est_bien_ordonne(R,E),  coincidence_univ }  ⊢  fusion_hyp(u,v,u',v').

    🎯 RÉDUCTION de la FUSION (Lemme 1 §III.2) à la SEULE COÏNCIDENCE.  Conclusion ==
    `ensembles_temoin_deux_couples.fusion_hyp(...)` LITTÉRALEMENT, i.e.
        temoin₁(u,v) ⇒ ( (u',v')∈h ⇒ temoin_commun_h(u,v,u',v') ),
    conditionnée UNIQUEMENT à :
      • est_bien_ordonne(R,E)  — arrière-plan structurel (R bien-ordonne E) ;
      • coincidence_univ       — la SEULE coïncidence géométrique reportée (Lemme 1).

    PREUVE.  Sous coeurA(u,v ; S,T,phi) et coeurB(u',v' ; Sb,Tb,pb) ASSUMÉS (witnesses
    VARIABLES distincts), _core_with_witnesses PROUVE temoin_commun_h(u,v,u',v')
    (comparabilité brique 1 + construction couvrante brique 2 + coïncidence).  On élimine
    les 3 ∃ de couple₂ (existe_elimination ; Sb,Tb,pb NON libres ailleurs), compose avec :
      • temoin₁[S,T,phi](u',v') ⇒ temoin₁[Sb,Tb,pb](u',v')  (_rename_temoin1, α-renommage) ;
      • (u',v')∈h ⇒ temoin₁[S,T,phi](u',v')  (h_membre_donne_temoin, CLOS) ;
    puis élimine les 3 ∃ de couple₁ ⇒ temoin₁(u,v) ⇒ ((u',v')∈h ⇒ tch) = fusion_hyp.
    theorie=22.  NON vacueux : fusion_hyp n'est aucune hypothèse.

    ⚠️ Les points u,v,u',v' sont les VARIABLES SCHÉMATIQUES ua,va,ub,vb (et non u,up,
    qui collisionneraient avec les binders internes « u »,« up » de est_bijective et
    déclencheraient un renommage parasite @ lors des éliminations existentielles).
    fusion_hyp étant un schéma sur les points, le prouver à ces variables = le prouver."""
    vu, vv, vup, vvp = _t(u), _t(v), _t(up), _t(vp)

    H_bo = N.assume(_bo_form(R, E_set))
    H_coinc = N.assume(coincidence_univ(E_set, R, F_set, Rp))

    # cœurs ASSUMÉS aux witnesses VARIABLES distincts (couple₁ : S,T,phi ; couple₂ : Sb,Tb,pb)
    coeurA = T2._coeur1(E_set, R, F_set, Rp, u, v, var(S), var(T), var(phi))
    coeurB = T2._coeur1(E_set, R, F_set, Rp, up, vp, var(Sb), var(Tb), var(pb))
    H_coeurA = N.assume(coeurA)
    H_coeurB = N.assume(coeurB)

    # cœur : temoin_commun_h(u,v,u',v')  sous { coeurA, coeurB, bo, coinc }
    tch = _core_with_witnesses(E_set, R, F_set, Rp, u, v, up, vp,
                               var(S), var(T), var(phi), var(Sb), var(Tb), var(pb),
                               H_coeurA, H_coeurB, H_bo, H_coinc)

    # — éliminer les 3 ∃ de couple₂ : coeurB ⇒ tch  ⟹  temoin₁[Sb,Tb,pb](u',v') ⇒ tch —
    impB = N.loi_deduction(coeurB, tch)              # coeurB(Sb,Tb,pb) ⇒ tch
    impB = existe_elimination(impB, pb)
    impB = existe_elimination(impB, Tb)
    impB = existe_elimination(impB, Sb)              # temoin₁[Sb,Tb,pb](u',v') ⇒ tch  [hyps : coeurA, bo, coinc]

    # — temoin₁[S,T,phi](u',v') ⇒ temoin₁[Sb,Tb,pb](u',v')  (α-renommage CLEAN par S5) —
    ren_imp, _ = _rename_temoin1(E_set, R, F_set, Rp, up, vp, S, T, phi, Sb, Tb, pb)
    impB2 = syllogisme(ren_imp, impB)               # temoin₁[S,T,phi](u',v') ⇒ tch

    # — composer (u',v')∈h ⇒ temoin₁[S,T,phi](u',v')  (h_membre_donne_temoin, CLOS) —
    hmdt = TS.h_membre_donne_temoin(E_set, R, F_set, Rp, "up", "vp", S, T, phi)
    hmdt_inst = instancie(instancie(hmdt, vup), vvp)   # (u',v')∈h ⇒ temoin₁[S,T,phi](u',v')
    imp_h = syllogisme(hmdt_inst, impB2)               # (u',v')∈h ⇒ tch   [hyps : coeurA, bo, coinc]

    # — éliminer les 3 ∃ de couple₁ : coeurA ⇒ ((u',v')∈h ⇒ tch) ⟹ temoin₁(u,v) ⇒ (…) —
    impA = N.loi_deduction(coeurA, imp_h)            # coeurA(S,T,phi) ⇒ ((u',v')∈h ⇒ tch)
    impA = existe_elimination(impA, phi)
    impA = existe_elimination(impA, T)
    impA = existe_elimination(impA, S)               # temoin₁(u,v) ⇒ ((u',v')∈h ⇒ tch)
    return impA                                      # = fusion_hyp   [hyps : bo, coinc]


def _bo_form(R, E_set):
    """est_bien_ordonne(R,E)  (R = graphe ; relation a≤b := (a,b)∈R)."""
    return E.est_bien_ordonne(_R_de(R), _t(E_set))


def fusion_depuis_coincidence_cible(E_set="E", R="R", F_set="F", Rp="Rp",
                                    u="ua", v="va", up="ub", vp="vb",
                                    S="S", T="T", phi="phi"):
    """ÉNONCÉ-cible (test miroir) :  fusion_hyp(u,v,u',v')  (= T2.fusion_hyp).

    ⚠️ Les points u,v,u',v' sont des VARIABLES SCHÉMATIQUES nommées ua,va,ub,vb
    (PAS u,up — qui collisionneraient avec les binders internes de est_bijective).
    fusion_hyp étant un schéma sur les points, le prouver à ces variables = le prouver."""
    return T2.fusion_hyp(E_set, R, F_set, Rp, u, v, up, vp, S, T, phi)


def fusion_depuis_coincidence_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les DEUX hypothèses survivantes (documentation / test miroir) :
       [ est_bien_ordonne(R,E),  coincidence_univ ]."""
    return [_bo_form(R, E_set), coincidence_univ(E_set, R, F_set, Rp)]


__all__ = [
    "coincidence_univ",
    "fusion_depuis_coincidence", "fusion_depuis_coincidence_cible",
    "fusion_depuis_coincidence_hypotheses",
]
