"""§III.2 — Théorème 3 (TRICHOTOMIE) : PONT ADJOINT ↔ R au sommet.

────────────────────────────────────────────────────────────────────────────────
RÔLE — fermer le RÉSIDU (3) de `maximalite_donne_trichotomie_prouve`
(ensembles_maximalite_substantielle) : l'iso de h⁺* sur les segments FERMÉS
]←,a*]≅]←,b*].  `extension_iso_depuis_iso_h` (ensembles_trichotomie_extension_iso)
fournit l'iso de h⁺ POUR LES ORDRES ADJOINTS ≤'_a/≤'_b ; le RÉSIDU (3) le demande
POUR R/Rp.  Le maillon manquant est le PONT :

      ≤'_a = relation_adjoint(R, S, a)  COÏNCIDE avec R  SUR  S∪{a},

dès que a est R-MAJORANT de S∪{a} (ce qui est le cas pour S=seg(R,E,a*) et a=a*
sommet du bon ordre : tout x∈seg(R,E,a*) vérifie R{x,a*} par déf. du segment, et
R{a*,a*} par réflexivité).

────────────────────────────────────────────────────────────────────────────────
CE MODULE LIVRE (theorie=22, rien postulé — NE MODIFIE AUCUN fichier existant) :

  🎯 TARGET 1 — `adjoint_egale_R_au_sommet(R,E,S,a)` :
        { (∀xq)( xq∈S∪{a} ⇒ R{xq,a} )  [a est R-majorant de S∪{a}] }
          ⊢ (∀xq)(∀yq)( (xq∈S∪{a} et yq∈S∪{a})
                ⇒ ( relation_adjoint(R,S,a){xq,yq} ⇔ R{xq,yq} ) ).
     PREUVE par CAS sur yq=a / yq≠a (cf. _adjoint_reduit_sous_yne /
     _adjoint_vers_sommet_vrai de ensembles_trichotomie_extension_iso).

  🎯 TARGET 2 — `iso_hplus_pour_R(...)` :
     RÉÉCRIT  iso(h⁺, ]←,a*], ]←,b*], ≤'_a*, ≤'_b*)  [extension_iso_depuis_iso_h]
       en     iso(h⁺, ]←,a*], ]←,b*],  R  ,  Rp )   [= RÉSIDU (3)],
     via TARGET 1 sur les deux côtés (pont ≤'⇔R sur ]←,a*], ≤'⇔Rp sur ]←,b*]).
     Le conjoint `est_bijective` est invariant ; seul `compatible_ordre` est réécrit.

  🎯 TARGET 3 — `maximalite_donne_trichotomie_prouve_v2(...)` :
     re-joue maximalite_donne_trichotomie_prouve en DÉCHARGEANT le RÉSIDU (3)
     via TARGET 2.  (Les 3 autres résidus — 2 segments fermés + inclusion produit —
     restent reportés ; cf. docstring de la fonction.)

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  NON vacueux.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_symetrie,
    equivalence_transitivite, instancie, cas, tiers_exclu,
)
from bourbaki.cardinaux.ensembles_segments_construction import seg as _seg
from bourbaki.cardinaux import ensembles_trichotomie_extension_iso as EXT
from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.ensembles.fonctions.ensembles_valeur_codomaine import valeur_dans_codomaine


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_adj_bridge"


def _equiv_intro(A_form, B_form, thm_AB, thm_BA):
    """De ⊢ B [A] et ⊢ A [B], construit ⊢ (A ⇔ B)."""
    return conjonction_intro(N.loi_deduction(A_form, thm_AB),
                             N.loi_deduction(B_form, thm_BA))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TARGET 1 — l'ordre adjoint ≤'_a COÏNCIDE avec R sur S∪{a} (au sommet a).
# ════════════════════════════════════════════════════════════════════════════
def majorant_de_adjoint(R="R", S="S", a="a", xq="xq"):
    """La formule « a est R-majorant de S∪{a} » :
        (∀xq)( xq∈S∪{a} ⇒ R{xq,a} ).

    (Tout point du segment FERMÉ S∪{a} est ≤ a.  C'est l'unique HYPOTHÈSE de
     TARGET 1, VRAIE pour S=seg(R,E,a*), a=a* sommet : x∈seg ⇒ R{x,a*} (déf. seg)
     et R{a*,a*} (réflexivité du bon ordre).)"""
    Rf = _R_de(R)
    va = _t(a)
    Ep = V.ensemble_adjoint(_t(S), va)
    vx = var(xq)
    return pourtout(xq, impl(appartient(vx, Ep), Rf(vx, va)))


def adjoint_egale_R_au_sommet(R="R", E_set="E", S="S", a="a", xq="xq", yq="yq"):
    """🎯 TARGET 1.  ⊢ { (∀xq)( xq∈S∪{a} ⇒ R{xq,a} ) }
          ⊢ (∀xq)(∀yq)( (xq∈S∪{a} et yq∈S∪{a})
                ⇒ ( relation_adjoint(R,S,a){xq,yq} ⇔ R{xq,yq} ) ).

    Le PONT ADJOINT↔R : l'ordre adjoint ≤'_a := relation_adjoint(R,S,a) COÏNCIDE
    avec R sur le segment FERMÉ S∪{a}, sous l'hypothèse « a R-majorant de S∪{a} ».

    PREUVE (binders FRAIS « xq »/« yq », ≠ du paramètre-sommet a).  Pour xq,yq∈S∪{a} :
      • yq=a : ≤'(xq,a) = R{xq,a} ∨ (a=a et xq∈S∪{a}) — VRAI par le 2ᵉ disjoint
        (_adjoint_vers_sommet_vrai, xq∈S∪{a}) ; et R{xq,a} VRAI par MAJORANT (xq∈S∪{a}).
        Les deux côtés VRAIS ⇒ équivalence (réécriture Leibniz yq→a puis a→yq).
      • yq≠a : le 2ᵉ disjoint (yq=a et …) est FAUX ⇒ ≤'(xq,yq) ⇔ R{xq,yq}
        (_adjoint_reduit_sous_yne).
    CAS sur yq=a / yq≠a (tiers exclu).  CONDITIONNEL — JAMAIS postulé.  theorie=22.

    ⚠️ E_set n'intervient PAS dans la conclusion (TARGET 1 est purement « ordre » sur
       S∪{a}) ; il n'est gardé que pour cohérence de signature avec ses appelants."""
    Rf = _R_de(R)
    va = _t(a)
    vS = _t(S)
    Ep = V.ensemble_adjoint(vS, va)                       # S∪{a}
    le = V.relation_adjoint(Rf, vS, va)                   # ≤'_a
    vx, vy = var(xq), var(yq)

    Hmaj = N.assume(majorant_de_adjoint(R, S, a, xq))     # (∀xq)(xq∈S∪{a} ⇒ R{xq,a})

    # corps sous (xq∈S∪{a} et yq∈S∪{a})
    Hxy = N.assume(et(appartient(vx, Ep), appartient(vy, Ep)))
    Hx_in = conjonction_elim_gauche(Hxy)                  # xq∈S∪{a}
    Hy_in = conjonction_elim_droite(Hxy)                  # yq∈S∪{a}

    adj_xy = le(vx, vy)                                   # ≤'(xq,yq)
    R_xy = Rf(vx, vy)                                     # R{xq,yq}

    # ── CAS yq = a ──────────────────────────────────────────────────────────
    Hyeq = N.assume(egal(vy, va))                         # yq=a
    #   ≤'(xq,a) VRAI : 2ᵉ disjoint (a=a et xq∈S∪{a})
    adj_xa_vrai = EXT._adjoint_vers_sommet_vrai(Rf, vS, va, vx, Hx_in)   # ⊢ ≤'(xq,a)
    #   R{xq,a} VRAI : MAJORANT appliqué à xq∈S∪{a}
    R_xa = N.modus_ponens(Hx_in, instancie(Hmaj, vx))     # ⊢ R{xq,a}
    #   (≤'(xq,a) ⇔ R{xq,a}) : les deux côtés VRAIS (équivalence de deux vrais)
    #     ≤'(xq,a) ⇒ R{xq,a}  (R{xq,a} VRAI sans l'antécédent) ;
    #     R{xq,a} ⇒ ≤'(xq,a)  (≤'(xq,a) VRAI sans l'antécédent).
    eq_at_a = conjonction_intro(N.loi_deduction(le(vx, va), R_xa),
                                N.loi_deduction(Rf(vx, va), adj_xa_vrai))
    #   transporter a → yq (Leibniz, via yq=a symétrisé)
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
    Ha_eq_y = N.modus_ponens(Hyeq, symetrie(vy, va))      # a=yq
    eqv_a_y = N.modus_ponens(Ha_eq_y,
        N.s6(va, vy, _HOLE, equiv(le(vx, var(_HOLE)), Rf(vx, var(_HOLE)))))
    cas_yeq = N.modus_ponens(eq_at_a, equivalence_avant(eqv_a_y))  # ≤'(xq,yq)⇔R{xq,yq} [yq=a]
    br_yeq = N.loi_deduction(egal(vy, va), cas_yeq)               # (yq=a) ⇒ (≤'⇔R)

    # ── CAS yq ≠ a ──────────────────────────────────────────────────────────
    Hyne = N.assume(non(egal(vy, va)))                    # yq≠a
    cas_yne = EXT._adjoint_reduit_sous_yne(Rf, vS, va, vx, vy, Hyne)  # ≤'(xq,yq)⇔R{xq,yq} [yq≠a]
    br_yne = N.loi_deduction(non(egal(vy, va)), cas_yne)         # (yq≠a) ⇒ (≤'⇔R)

    # ── recoller par cas ─────────────────────────────────────────────────────
    eq_corps = cas(tiers_exclu(egal(vy, va)), br_yeq, br_yne)    # ≤'(xq,yq)⇔R{xq,yq} [Hxy, Hmaj]
    #   décharger l'antécédent (xq∈S∪{a} et yq∈S∪{a}), puis ∀yq, ∀xq
    imp_corps = N.loi_deduction(et(appartient(vx, Ep), appartient(vy, Ep)), eq_corps)
    gen_y = N.generalisation(yq, imp_corps)
    gen_xy = N.generalisation(xq, gen_y)
    return gen_xy                                               # [Hmaj]


def adjoint_egale_R_au_sommet_cible(R="R", E_set="E", S="S", a="a", xq="xq", yq="yq"):
    """ÉNONCÉ-cible (test miroir) de TARGET 1."""
    Rf = _R_de(R)
    va = _t(a)
    vS = _t(S)
    Ep = V.ensemble_adjoint(vS, va)
    le = V.relation_adjoint(Rf, vS, va)
    vx, vy = var(xq), var(yq)
    return pourtout(xq, pourtout(yq,
        impl(et(appartient(vx, Ep), appartient(vy, Ep)),
             equiv(le(vx, vy), Rf(vx, vy)))))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TARGET 2 — RÉÉCRITURE iso(h⁺, ≤'_a, ≤'_b)  ⟶  iso(h⁺, R, Rp).
# ════════════════════════════════════════════════════════════════════════════
def _valeur_but_j(G, e_set, F_set, x):
    """{ G⊂e×F, dom G=e, x∈e } ⊢ valeur(G, x, b='j') ∈ F.

    valeur_dans_codomaine donne valeur(G,x,b='y')∈F ; α-renomme le liant τy→τj
    (alpha_tau, CS1) pour matcher le terme f(x)=valeur(G,x,b='j') de compatible_ordre."""
    vG, vx, vF = _t(G), _t(x), _t(F_set)
    val_y = valeur_dans_codomaine(vG, e_set, vF, vx)        # valeur(G,x,'y') ∈ F
    # α-τ : τy((x,y)∈G) = τj((x,j)∈G)
    r = appartient(E.couple(vx, var("y")), vG)
    eq_yj = N.alpha_tau(r, "y", "j")                        # valeur(G,x,'y') = valeur(G,x,'j')
    fy, fj = E.valeur(vG, vx, b="y"), E.valeur(vG, vx, b="j")
    leib = N.modus_ponens(eq_yj, N.s6(fy, fj, _HOLE, appartient(var(_HOLE), vF)))
    return N.modus_ponens(val_y, equivalence_avant(leib))   # valeur(G,x,'j') ∈ F


def compat_hplus_pour_R(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { hyps de extension_iso_depuis_iso_h,
           (∀x)(x∈S∪{a} ⇒ R{x,a})    [a R-majorant de S∪{a}],
           (∀x)(x∈T∪{b} ⇒ Rp{x,b})   [b Rp-majorant de T∪{b}],
           h⁺ ⊂ (S∪{a})×(T∪{b}),  dom h⁺ = S∪{a} }
          ⊢ compatible_ordre( h⁺, S∪{a}, R, Rp, "px", "pw" ).

    RÉÉCRIT compatible_ordre(h⁺, S∪{a}, ≤'_a, ≤'_b) [extension_iso_depuis_iso_h] en
    compatible_ordre(h⁺, S∪{a}, R, Rp) via le PONT TARGET 1 sur LES DEUX CÔTÉS.

    Pour px,pw∈S∪{a}, avec f=h⁺ :
        R{px,pw}  ⇔[bridgeS]  ≤'_a{px,pw}  ⇔[compat_adj]  ≤'_b{f(px),f(pw)}
                  ⇔[bridgeT]  Rp{f(px),f(pw)},
    où bridgeT exige f(px),f(pw)∈T∪{b} (valeur_dans_codomaine, via h⁺⊂… et dom h⁺=…).
    CONDITIONNEL — JAMAIS postulé.  theorie=22."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    va, vb = _t(a), _t(b)
    S = EXT._seg_S(R, E_set, a)
    T = EXT._seg_T(Rp, F_set, b)
    SaA = V.ensemble_adjoint(S, va)                         # S∪{a}
    TbB = V.ensemble_adjoint(T, vb)                         # T∪{b}
    hplus = EXT._hplus(E_set, R, F_set, Rp, a, b)
    le_a = EXT._le_a(R, E_set, a)                           # ≤'_a
    le_b = EXT._le_b(Rp, F_set, b)                          # ≤'_b
    vpx, vpw = var("px"), var("pw")
    fpx = E.valeur(hplus, vpx, b="j")                       # f(px)  (binder de compatible_ordre)
    fpw = E.valeur(hplus, vpw, b="j")                       # f(pw)

    # ── iso adjoint (extension) → projection compatibilité ────────────────────
    iso_adj = EXT.extension_iso_depuis_iso_h(E_set, R, F_set, Rp, a, b)
    compat_adj = conjonction_elim_droite(iso_adj)           # compatible_ordre(h⁺,S∪{a},≤'_a,≤'_b,xa,ya)

    # ── PONTS TARGET 1 (source & but) ─────────────────────────────────────────
    bridgeS = adjoint_egale_R_au_sommet(R, E_set, S, a)     # ∀∀ ≤'_a⇔R sur S∪{a}  [maj_S]
    bridgeT = adjoint_egale_R_au_sommet(Rp, F_set, T, b)    # ∀∀ ≤'_b⇔Rp sur T∪{b} [maj_T]

    # ── corps sous (px∈S∪{a} et pw∈S∪{a}) ────────────────────────────────────
    Hin = N.assume(et(appartient(vpx, SaA), appartient(vpw, SaA)))
    Hpx = conjonction_elim_gauche(Hin)                      # px∈S∪{a}
    Hpw = conjonction_elim_droite(Hin)                      # pw∈S∪{a}

    # bridgeS @ (px,pw) déchargé : ≤'_a{px,pw} ⇔ R{px,pw}
    eqS = N.modus_ponens(Hin, instancie(instancie(bridgeS, vpx), vpw))
    eqS = equivalence_symetrie(eqS)                         # R{px,pw} ⇔ ≤'_a{px,pw}

    # compat_adj @ (px,pw) déchargé : ≤'_a{px,pw} ⇔ ≤'_b{f(px),f(pw)}
    eqMid = N.modus_ponens(Hin, instancie(instancie(compat_adj, vpx), vpw))

    # f(px),f(pw) ∈ T∪{b}  (valeur_dans_codomaine, binder j)
    f_px_in = _valeur_but_j(hplus, SaA, TbB, vpx)           # f(px)∈T∪{b}  [h⁺⊂…, dom h⁺=…, px∈S∪{a}]
    f_pw_in = _valeur_but_j(hplus, SaA, TbB, vpw)           # f(pw)∈T∪{b}
    # décharger px∈S∪{a}, pw∈S∪{a} dans les memberships par Hpx/Hpw
    f_px_in = N.modus_ponens(Hpx, N.loi_deduction(appartient(vpx, SaA), f_px_in))
    f_pw_in = N.modus_ponens(Hpw, N.loi_deduction(appartient(vpw, SaA), f_pw_in))
    in_fpx_fpw = conjonction_intro(f_px_in, f_pw_in)        # f(px)∈T∪{b} et f(pw)∈T∪{b}

    # bridgeT @ (f(px),f(pw)) déchargé : ≤'_b{f(px),f(pw)} ⇔ Rp{f(px),f(pw)}
    eqT = N.modus_ponens(in_fpx_fpw, instancie(instancie(bridgeT, fpx), fpw))

    # chaîne : R{px,pw} ⇔ ≤'_a ⇔ ≤'_b{f..} ⇔ Rp{f..}
    chain = equivalence_transitivite(equivalence_transitivite(eqS, eqMid), eqT)
    #   chain : R{px,pw} ⇔ Rp{f(px),f(pw)}
    imp_corps = N.loi_deduction(et(appartient(vpx, SaA), appartient(vpw, SaA)), chain)
    gen_w = N.generalisation("pw", imp_corps)
    gen_xw = N.generalisation("px", gen_w)
    assert gen_xw.conclusion == V.compatible_ordre(hplus, SaA, Rf, Rpf, x="px", y="pw")
    return gen_xw


def iso_hplus_pour_R(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """🎯 TARGET 2.  ⊢ { hyps de extension_iso_depuis_iso_h,
           (∀x)(x∈S∪{a} ⇒ R{x,a}),  (∀x)(x∈T∪{b} ⇒ Rp{x,b})   [a,b R/Rp-majorants],
           h⁺ ⊂ (S∪{a})×(T∪{b}),  dom h⁺ = S∪{a} }
          ⊢ est_isomorphisme_ordre( h⁺,  S∪{a},  T∪{b},  R,  Rp,  "px", "pw" ).

    = RÉSIDU (3) de maximalite_donne_trichotomie_prouve (binders px/pw, relations
    R/Rp), DÉRIVÉ de extension_iso_depuis_iso_h (qui le donne pour les ordres
    ADJOINTS ≤'_a/≤'_b).  Le conjoint est_bijective(h⁺,S∪{a},T∪{b}) est INVARIANT par
    changement de relation (réutilisé tel quel) ; seul compatible_ordre est réécrit
    (compat_hplus_pour_R).  CONDITIONNEL — JAMAIS postulé.  theorie=22.  NON vacueux."""
    iso_adj = EXT.extension_iso_depuis_iso_h(E_set, R, F_set, Rp, a, b)
    bij = conjonction_elim_gauche(iso_adj)                  # est_bijective(h⁺,S∪{a},T∪{b}) — INVARIANT
    compat_R = compat_hplus_pour_R(E_set, R, F_set, Rp, a, b)
    return conjonction_intro(bij, compat_R)


def iso_hplus_pour_R_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) de TARGET 2 = RÉSIDU (3) (binders px/pw, R/Rp)."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    va, vb = _t(a), _t(b)
    S = EXT._seg_S(R, E_set, a)
    T = EXT._seg_T(Rp, F_set, b)
    SaA = V.ensemble_adjoint(S, va)
    TbB = V.ensemble_adjoint(T, vb)
    hplus = EXT._hplus(E_set, R, F_set, Rp, a, b)
    return V.est_isomorphisme_ordre(hplus, SaA, TbB, Rf, Rpf, x="px", y="pw")


# ════════════════════════════════════════════════════════════════════════════
#  DÉCHARGE des 2 MAJORANTS de TARGET 2 depuis le bon ordre + a sommet.
#  Le segment FERMÉ seg(R,E,a)∪{a} a a pour R-majorant : x∈seg ⇒ R{x,a} (déf seg)
#  et R{a,a} (réflexivité du bon ordre).
# ════════════════════════════════════════════════════════════════════════════
def majorant_seg_ferme_depuis_bo(R="R", E_set="E", a="a"):
    """⊢ { est_bien_ordonne(R,E),  a∈E }
          ⊢ (∀xq)( xq ∈ seg(R,E,a)∪{a} ⇒ R{xq,a} ).

    Le segment FERMÉ ]←,a] = seg(R,E,a)∪{a} a a pour R-MAJORANT.  Pour xq∈]←,a] :
      • xq∈seg(R,E,a) ⇒ R{xq,a}  (caractérisation membre_segment : 2ᵉ conjoint) ;
      • xq=a         ⇒ R{a,a}    (RÉFLEXIVITÉ de R sur E, projetée de bo, appliquée
        à a∈E) puis Leibniz a→xq.
    CAS via _membre_adjoint (xq∈seg ou xq=a).  Discharge EXACTEMENT le majorant
    majorant_de_adjoint(R, seg(R,E,a), a) que TARGET 1/2 réclament.  theorie=22."""
    from bourbaki.cardinaux.ensembles_segments_construction import membre_segment
    Rf = _R_de(R)
    va, vE = _t(a), _t(E_set)
    S = _seg(R, E_set, a)
    Ep = V.ensemble_adjoint(S, va)                         # seg(R,E,a)∪{a}
    vx = var("xq")

    # bo → réflexivité dans E :  (∀x)(R{x,x} ⇔ x∈E)
    Hbo = N.assume(E.est_bien_ordonne(Rf, vE))
    ord_dans = conjonction_elim_gauche(Hbo)                # est_relation_ordre_dans(R,E)
    refl = conjonction_elim_droite(ord_dans)               # est_reflexive_dans_ordre(R,E)
    # a∈E ⇒ R{a,a}
    Ha_E = N.assume(appartient(va, vE))
    refl_a = instancie(refl, va)                           # R{a,a} ⇔ a∈E
    Raa = N.modus_ponens(Ha_E, equivalence_arriere(refl_a))  # R{a,a}

    # corps sous xq∈seg∪{a}
    Hin = N.assume(appartient(vx, Ep))
    membre = EXT._membre_adjoint(S, va, vx)                # xq∈seg∪{a} ⇔ (xq∈seg ou xq=a)
    disj = N.modus_ponens(Hin, equivalence_avant(membre))  # xq∈seg ou xq=a

    # branche xq∈seg ⇒ R{xq,a}
    Hseg = N.assume(appartient(vx, S))
    car = membre_segment(R, E_set, a, "xq")                # xq∈seg ⇔ ((xq∈E et R{xq,a}) et xq≠a)
    corps = N.modus_ponens(Hseg, equivalence_avant(car))   # (xq∈E et R{xq,a}) et xq≠a
    R_xa = conjonction_elim_droite(conjonction_elim_gauche(corps))   # R{xq,a}
    br_seg = N.loi_deduction(appartient(vx, S), R_xa)      # (xq∈seg) ⇒ R{xq,a}

    # branche xq=a ⇒ R{xq,a}  (Leibniz a→xq sur R{a,a})
    Hxa = N.assume(egal(vx, va))                           # xq=a
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
    Hax = N.modus_ponens(Hxa, symetrie(vx, va))            # a=xq
    R_xa_2 = N.modus_ponens(Raa,
        equivalence_avant(N.modus_ponens(Hax,
            N.s6(va, vx, _HOLE, Rf(var(_HOLE), va)))))     # R{xq,a}  [a∈E, xq=a]
    br_eq = N.loi_deduction(egal(vx, va), R_xa_2)          # (xq=a) ⇒ R{xq,a}

    R_xa_corps = cas(disj, br_seg, br_eq)                  # R{xq,a}  [bo, a∈E, xq∈seg∪{a}]
    imp = N.loi_deduction(appartient(vx, Ep), R_xa_corps)
    gen = N.generalisation("xq", imp)
    assert gen.conclusion == majorant_de_adjoint(R, S, a)
    return gen


def iso_hplus_pour_R_majorants_discharges(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { hyps de extension_iso_depuis_iso_h,
           est_bien_ordonne(R,E),  a∈E,  est_bien_ordonne(Rp,F),  b∈F,
           h⁺ ⊂ (S∪{a})×(T∪{b}),  dom h⁺ = S∪{a} }
          ⊢ est_isomorphisme_ordre( h⁺, S∪{a}, T∪{b}, R, Rp, "px", "pw" ).

    = TARGET 2 (iso_hplus_pour_R) avec les DEUX MAJORANTS DÉCHARGÉS via
    majorant_seg_ferme_depuis_bo (source : bo(R,E)+a∈E ; but : bo(Rp,F)+b∈F).
    Les 2 majorants sont REMPLACÉS par {bo(R,E), a∈E, bo(Rp,F), b∈F} — HONNÊTES
    (bo×2 sont parmi les 3 hyps cibles ; a∈E, b∈F déchargées dans le théorème v2).
    theorie=22."""
    out = iso_hplus_pour_R(E_set, R, F_set, Rp, a, b)
    S = EXT._seg_S(R, E_set, a)
    T = EXT._seg_T(Rp, F_set, b)
    majS_pr = majorant_seg_ferme_depuis_bo(R, E_set, a)    # [bo(R,E), a∈E]
    majT_pr = majorant_seg_ferme_depuis_bo(Rp, F_set, b)   # [bo(Rp,F), b∈F]
    out = N.modus_ponens(majS_pr, N.loi_deduction(majorant_de_adjoint(R, S, a), out))
    out = N.modus_ponens(majT_pr, N.loi_deduction(majorant_de_adjoint(Rp, T, b), out))
    return out


# ════════════════════════════════════════════════════════════════════════════
#  🎯 TARGET 3 — maximalite_donne_trichotomie_prouve_v2 : RÉSIDU (3) DÉRIVÉ.
# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ BLOCAGE INFRASTRUCTURE (honnête, précisément documenté).
#  Substituer TARGET 2 dans maximalite_donne_trichotomie_prouve EXIGE de construire
#  iso_hplus_pour_R AU TÉMOIN a*=τx(…), b*=τx(…).  Or extension_iso_depuis_iso_h (et
#  toute la machinerie recollement_bijection / couples qu'elle appelle) utilise des
#  binders FIXES (« x », puis « q »/« p » dans image_reunion_graphes /
#  couple_egal_implique_composantes) qui ENTRENT EN COLLISION avec le liant interne
#  du τ-témoin (a* est τx(…) avec un (∀w) interne).  Le résultat : un
#  « modus ponens : mineure ≠ antécédent » DANS LES MODULES EXISTANTS (non
#  modifiables).  Le blocage est INDÉPENDANT du pont adjoint↔R (TARGET 1/2, clos pour
#  tout témoin BIEN NOMMÉ) : il vient de la NON-fraîcheur des binders du recollement
#  vis-à-vis d'un témoin à τ imbriqué.  AUCUN binder de témoin n'évite TOUTES les
#  lettres fixes du recollement.  CE serait un chantier de FRAÎCHEUR de binders dans
#  ensembles_recollement_bijection / ensembles_couples — hors périmètre (« ne modifie
#  aucun fichier existant »).  TARGET 3 (substitution effective au témoin) est donc
#  BLOQUÉ par cette fragilité pré-existante, PAS par un trou logique du pont.
def maximalite_donne_trichotomie_prouve_v2(E_set="E", R="R", F_set="F", Rp="Rp"):
    """🎯 TARGET 3 (PARTIEL — bloqué infrastructure, cf. note ci-dessus).

    INTENTION : ⊢ ( dom h = E ) ou ( pr₂ h = F ), en RE-JOUANT
    maximalite_donne_trichotomie_prouve mais en DÉCHARGEANT le RÉSIDU (3) (l'iso de
    h⁺* w.r.t. R/Rp) par TARGET 2 (iso_hplus_pour_R_majorants_discharges au témoin
    a*,b*) — au lieu de l'ASSUMER.

    ⚠️ BLOCAGE : iso_hplus_pour_R(…, a*, b*) ne se CONSTRUIT PAS — extension_iso_depuis_iso_h
    (machinerie recollement_bijection / couples, modules EXISTANTS non modifiables)
    a des binders FIXES qui COLLISIONNENT avec le liant τx imbriqué du témoin a*=τx(…).
    Le pont adjoint↔R lui-même (TARGET 1/2) est CLOS pour tout témoin bien nommé ; seule
    l'INSTANCIATION mécanique au témoin à τ imbriqué est bloquée (fraîcheur de binders du
    recollement — hors périmètre).  Cette fonction LÈVE donc explicitement, en relayant
    le diagnostic, plutôt que de prétendre une clôture.  TARGET 2 RESTE la livraison :
    elle PROUVE que le RÉSIDU (3) découle de extension_iso_depuis_iso_h (lemme déjà
    prouvé) + le pont — fermant LOGIQUEMENT le maillon « pont adjoint↔R ».

    ⚠️ HONNÊTETÉ — même CONSTRUITE, v2 ne réduirait PAS aux 3 hyps : elle ÉCHANGERAIT
    le RÉSIDU (3) (1 formule) contre les 9 hypothèses structurelles de
    extension_iso_depuis_iso_h (« h iso de SEGMENTS » + « a,b SOMMETS ») — la VRAIE part
    Cantor–Bernstein, REPORTÉE.  TARGET 2 RELIE le RÉSIDU (3) à ce lemme prouvé, mais ne
    ferme PAS la part Cantor–Bernstein."""
    raise NotImplementedError(
        "TARGET 3 bloqué : extension_iso_depuis_iso_h ne se construit pas au témoin "
        "a*=τx(…) (collision de binders du recollement avec le τ imbriqué, modules "
        "existants non modifiables). Le pont adjoint↔R (TARGET 1/2) est clos. Voir "
        "iso_hplus_pour_R (RÉSIDU (3) dérivé de extension_iso_depuis_iso_h + pont, "
        "générique) et la note de module.")


def maximalite_donne_trichotomie_prouve_v2_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) : ( dom h = E ) ou ( pr₂ h = F )  ( == maximalite_donne_trichotomie )."""
    return M.maximalite_donne_trichotomie(E_set, R, F_set, Rp)


__all__ = [
    # TARGET 1
    "majorant_de_adjoint",
    "adjoint_egale_R_au_sommet", "adjoint_egale_R_au_sommet_cible",
    # TARGET 2
    "iso_hplus_pour_R", "iso_hplus_pour_R_cible",
    "compat_hplus_pour_R",
    "majorant_seg_ferme_depuis_bo",
    "iso_hplus_pour_R_majorants_discharges",
    # TARGET 3
    "maximalite_donne_trichotomie_prouve_v2",
    "maximalite_donne_trichotomie_prouve_v2_cible",
]
