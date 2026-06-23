"""§III.2 — Théorème 3 (TRICHOTOMIE) : MAXIMALITÉ SUBSTANTIELLE de l'iso maximal h.

────────────────────────────────────────────────────────────────────────────────
RÔLE — le DERNIER maillon dur de la trichotomie (Théorème 3 §III.2).  L'iso maximal
h = h_iso_max(E,R,F,Rp) (union des graphes d'iso d'APPLICATIONS de segments) a :

  • ses 3 COHÉRENCES PROUVÉES sous {bo(R,E), bo(R',F), residu_univ_app} :
      est_fonctionnel(h)        ← ensembles_maillon_coherences_prouvees.fonctionnel_h_prouve
      compatibilite_inverse_h   ← ensembles_h_bien_defini.compatibilite_inverse_h_prouve
      compatibilite_ordre_h     ← ensembles_h_bien_defini.compatibilite_ordre_h_prouve

CE MODULE LIVRE (theorie=22, rien postulé — NE MODIFIE AUCUN fichier existant) :

  🎯🎯 TARGET A — `h_est_iso_prouve(...)` :
        { bo(R,E), bo(R',F), residu_univ_app }
          ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).
     ASSEMBLE h_est_isomorphisme_ordre_sous_hyp (ensembles_trichotomie_h_iso) en
     DÉCHARGEANT ses 4 hypothèses :
       • est_fonctionnel(h)        ← fonctionnel_h_prouve              (PROUVÉE) ;
       • compatibilite_inverse_h   ← compatibilite_inverse_h_prouve    (PROUVÉE) ;
       • compatibilite_ordre_h     ← compatibilite_ordre_h_prouve      (PROUVÉE) ;
       • est_surjective(h,dom h,pr₂ h) = (image(h,dom h)=pr₂ h)        ← `_h_surjective`
         (PROUVÉE INCONDITIONNELLEMENT : pr₂(h) EST l'image de h sur dom h).

  🎯🎯 TARGET B — `maximalite_donne_trichotomie_prouve(...)` :
        { bo(R,E), bo(R',F), residu_univ_app, h_maximal }
          ⊢ ( dom h = E )  ou  ( pr₂ h = F )   (== maximalite_donne_trichotomie).
     PREUVE par CONTRADICTION (back-and-forth, magnitude Cantor–Bernstein) :
       Supposons dom h≠E ∧ pr₂h≠F.  Comme dom h⊂E (h_dom_inclus_E) propre, a:=min(E∖dom h)
       et dom h=seg(R,E,a), a∉dom h (prop1_segment_propre_clos) ; symétriquement b,
       pr₂h=seg(Rp,F,b), b∉pr₂h.  h⁺:=h∪{(a,b)} est un iso de segments ]←,a]≅]←,b]
       (extension_iso_depuis_iso_h, alimenté par TARGET A).  Comme h⁺ est l'iso d'une
       APPLICATION de segments, (a,b)∈h (couple_iso_dans_h).  Mais (a,b)∈h ⇒ a∈dom h,
       contredisant a∉dom h.  D'où dom h=E ∨ pr₂h=F.

INVARIANT : theorie_ensembles() = 22.  Rien postulé.  Hypothèses HONNÊTES
{bo(R,E), bo(R',F), residu_univ_app} + h_maximal (B).  NON vacueux : aucune
conclusion n'est une de ses hypothèses.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis import ensembles_ordre_vocab as V
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, projection_droite,
    cas, tiers_exclu,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie, composer_egalites

from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.assemblage import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.maximalite import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.h_coherences import ensembles_trichotomie_h_iso as HI
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.h_coherences import ensembles_h_bien_defini as HBD
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.assemblage import ensembles_maillon_coherences_prouvees as MCP
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.coincidence_fusion import ensembles_fusion_depuis_coincidence_app as FDA
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.maximalite import ensembles_trichotomie_maximalite_preuve as MP
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.assemblage import ensembles_trichotomie_temoin_adjonction as ADJ
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.temoins_comparabilite import ensembles_trichotomie_prop1 as P1
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import seg as _seg


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation portée par le graphe R : a≤b := (a,b)∈R  (convention projet)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


_HOLE = "hole_maxsub"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b et ⊢ Φ[a] déduit ⊢ Φ[b]   (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_falso(thm_a, thm_na, z):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.  (ex falso quodlibet, S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P  (via S1)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ SURJECTIVITÉ INCONDITIONNELLE : pr₂(h) EST l'image de h sur dom(h).
#     est_surjective(h, dom h, pr₂ h) = ( image(h, dom h) = pr₂ h ).
# ════════════════════════════════════════════════════════════════════════════
def image_dom_egale_img(g="G"):
    """⊢ image(G, dom G) = pr₂(G).   (INCONDITIONNEL, theorie=22.)

    Double inclusion + extensionnalité A1 :
      (⊂)  z∈G⟨dom G⟩ ⇒ (∃x)(x∈dom G et (x,z)∈G) ⇒ (∃x)((x,z)∈G) ⇒ z∈pr₂G.
      (⊃)  z∈pr₂G ⇒ (∃x)((x,z)∈G) ; pour un tel x, (x,z)∈G ⇒ x∈dom G (AXIOME_DOM,
           témoin z), donc (x∈dom G et (x,z)∈G), d'où z∈G⟨dom G⟩.
    Binder élément « z » (canonique de inclus / A1).  L'AXIOME_DOM est instancié
    avec le couple (x, z) : son liant interne ∃y est α-renommé en « z » par
    instanciation de la projection (les deux ∃ alors COÏNCIDENT)."""
    vg = _t(g)
    domg = E.dom(vg)
    img_g = E.img(vg)
    image_g = E.image(vg, domg)
    vx, vz = var("x"), var("z")

    ax_img = N.axiome(E.theorie_ensembles(), E.AXIOME_IMG)
    ax_image = N.axiome(E.theorie_ensembles(), E.AXIOME_IMAGE)
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    img_eq = instancie(instancie(ax_img, vg), vz)            # z∈pr₂G ⇔ (∃x)((x,z)∈G)
    image_eq = instancie(instancie(instancie(ax_image, vg), domg), vz)
    #   z∈G⟨dom G⟩ ⇔ (∃x)(x∈dom G et (x,z)∈G)

    couple_xz = appartient(E.couple(vx, vz), vg)             # (x,z)∈G
    body_image = et(appartient(vx, domg), couple_xz)         # x∈dom G et (x,z)∈G

    # ── (⊂)  image(G,dom G) ⊂ pr₂G ──
    proj = projection_droite(appartient(vx, domg), couple_xz)   # body_image ⇒ (x,z)∈G
    mono_g = monotonie_existe(proj, "x")                     # (∃x)body_image ⇒ (∃x)(x,z)∈G
    z_imp_fwd = syllogisme(equivalence_avant(image_eq),
                           syllogisme(mono_g, equivalence_arriere(img_eq)))   # z∈image ⇒ z∈pr₂G
    incl_image_img = N.generalisation("z", z_imp_fwd)        # image(G,domG) ⊂ pr₂G

    # ── (⊃)  pr₂G ⊂ image(G,dom G) ──
    #   pour (x,z)∈G : x∈dom G via AXIOME_DOM (instancié au couple (x, ·), témoin z)
    Hxz = N.assume(couple_xz)                                # (x,z)∈G
    dom_eq_x = instancie(instancie(ax_dom, vg), vx)          # x∈dom G ⇔ (∃y)((x,y)∈G)
    #   (∃y)((x,y)∈G) — témoin y:=z
    ex_xy = N.modus_ponens(Hxz, N.s5(appartient(E.couple(vx, var("y")), vg), vz, "y"))
    x_in_dom = N.modus_ponens(ex_xy, equivalence_arriere(dom_eq_x))   # x∈dom G
    body_proof = conjonction_intro(x_in_dom, Hxz)            # x∈dom G et (x,z)∈G  [(x,z)∈G]
    couple_to_body = N.loi_deduction(couple_xz, body_proof)  # (x,z)∈G ⇒ body_image
    mono_back = monotonie_existe(couple_to_body, "x")        # (∃x)(x,z)∈G ⇒ (∃x)body_image
    z_imp_bwd = syllogisme(equivalence_avant(img_eq),
                           syllogisme(mono_back, equivalence_arriere(image_eq)))  # z∈pr₂G ⇒ z∈image
    incl_img_image = N.generalisation("z", z_imp_bwd)        # pr₂G ⊂ image(G,domG)

    # ── A1 : (image⊂pr₂G et pr₂G⊂image) ⇒ image=pr₂G ──
    a1 = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), image_g), img_g)
    return N.modus_ponens(conjonction_intro(incl_image_img, incl_img_image), a1)


def image_dom_egale_img_cible(g="G"):
    """ÉNONCÉ-cible (test miroir) :  image(G, dom G) = pr₂(G)."""
    vg = _t(g)
    return egal(E.image(vg, E.dom(vg)), E.img(vg))


def _h_surjective(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ est_surjective(h, dom h, pr₂ h).   (INCONDITIONNEL, theorie=22.)

    est_surjective(h, dom h, pr₂ h) := ( image(h, dom h) = pr₂ h ) — c'est
    EXACTEMENT image_dom_egale_img(h), pr₂(h) ÉTANT l'image de h sur dom h."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    res = image_dom_egale_img(h)
    assert res.conclusion == E.est_surjective(h, E.dom(h), E.img(h))
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 TARGET A — h est un ISOMORPHISME D'ORDRE de dom h sur pr₂ h (PROUVÉ).
# ════════════════════════════════════════════════════════════════════════════
def h_est_iso_prouve(E_set="E", R="R", F_set="F", Rp="Rp"):
    """⊢ { bo(R,E), bo(R',F), residu_univ_app }
          ⊢ est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp).

    🎯🎯 TARGET A.  h = h_iso_max est un ISOMORPHISME D'ORDRE de dom(h)=S₀ sur
    pr₂(h)=T₀.  On ASSEMBLE `h_est_isomorphisme_ordre_sous_hyp`
    (ensembles_trichotomie_h_iso) en DÉCHARGEANT ses 4 hypothèses :
      • est_fonctionnel(h)        ← MCP.fonctionnel_h_prouve            (PROUVÉE) ;
      • compatibilite_inverse_h   ← HBD.compatibilite_inverse_h_prouve  (PROUVÉE) ;
      • compatibilite_ordre_h     ← HBD.compatibilite_ordre_h_prouve    (PROUVÉE) ;
      • est_surjective(h,dom h,pr₂ h) ← _h_surjective (INCONDITIONNELLE : pr₂(h)
        est l'image de h sur dom h, image_dom_egale_img).
    Il ne SURVIT que {bo(R,E), bo(R',F), residu_univ_app} (les hypothèses HONNÊTES
    portées par les 3 preuves de cohérence).  theorie=22, rien postulé, NON vacueux :
    est_isomorphisme_ordre(...) n'est aucune hypothèse."""
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis (schéma coincidence_univ_app)"
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)

    # le séquent conditionnel à 4 hypothèses
    iso_sous = HI.h_est_isomorphisme_ordre_sous_hyp(E_set, R, F_set, Rp)

    # les 4 PREUVES
    func_pr = MCP.fonctionnel_h_prouve(E_set, R, F_set, Rp)        # est_fonctionnel(h)
    inv_pr = HBD.compatibilite_inverse_h_prouve(E_set, R, F_set, Rp)  # compatibilite_inverse_h
    ord_pr = HBD.compatibilite_ordre_h_prouve(E_set, R, F_set, Rp)    # compatibilite_ordre_h
    surj_pr = _h_surjective(E_set, R, F_set, Rp)                   # est_surjective(h,dom h,pr₂ h)

    # les 4 FORMULES-hypothèses (depuis la SOURCE canonique)
    f_func = E.est_fonctionnel(h)
    f_inv = HI.compatibilite_inverse_h(E_set, R, F_set, Rp)
    f_ord = HI.compatibilite_ordre_h(E_set, R, F_set, Rp)
    f_surj = E.est_surjective(h, domh, imgh)

    # décharge des 4 hypothèses par leurs preuves
    out = iso_sous
    for hyp_form, preuve in [(f_func, func_pr), (f_inv, inv_pr),
                             (f_ord, ord_pr), (f_surj, surj_pr)]:
        assert preuve.conclusion == hyp_form, \
            f"preuve ne conclut pas l'hypothèse: {preuve.conclusion} != {hyp_form}"
        out = N.modus_ponens(preuve, N.loi_deduction(hyp_form, out))
    return out


def h_est_iso_prouve_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) :  est_isomorphisme_ordre(h, dom h, pr₂ h, R, Rp)."""
    return HI.h_est_isomorphisme_ordre_sous_hyp_cible(E_set, R, F_set, Rp)


def h_est_iso_prouve_hypotheses(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Les 2 HYPOTHÈSES SURVIVANTES (documentation / test miroir) de TARGET A :
       [ bo(R,E), bo(R',F) ]  (= celles des cohérences prouvées).
       ⚠️ `residu_univ_app` ÉLIMINÉ (dérivé de residu_univ_app_renforce, CLOS)."""
    return FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp)


# ════════════════════════════════════════════════════════════════════════════
#  TARGET B — MAXIMALITÉ SUBSTANTIELLE : dom h = E  ou  pr₂ h = F.
#  Back-and-forth (magnitude Cantor–Bernstein).
# ════════════════════════════════════════════════════════════════════════════
#
#  TERMES-TÉMOINS de l'adjonction du sommet (h⁺ = h ∪ {(a,b)}, S=]←,a], T=]←,b]).
def _hplus(E_set, R, F_set, Rp, a, b):
    """h⁺ := h ∪ {(a,b)}   (témoin d'extension par le sommet, ensembles_*_temoin_adjonction)."""
    return ADJ.temoin_adjonction(E_set, R, F_set, Rp, a, b)


def _Saa(R, E_set, a):
    """]←,a] := seg(R,E,a) ∪ {a}   (segment FERMÉ d'extrémité a)."""
    return V.ensemble_adjoint(_seg(R, E_set, a), _t(a))


def _Tbb(Rp, F_set, b):
    """]←,b] := seg(Rp,F,b) ∪ {b}   (segment FERMÉ d'extrémité b)."""
    return V.ensemble_adjoint(_seg(Rp, F_set, b), _t(b))


# ── PIÈCES PROUVÉES du couple-iso-dans-h pour le témoin h⁺ (génériques a,b) ──
def _a_dans_Saa(R="R", E_set="E", a="a"):
    """⊢ a ∈ ]←,a] = seg(R,E,a)∪{a}.   (INCONDITIONNEL : a∈{a} ⇒ a∈seg∪{a}.)"""
    from bourbaki.ensembles.ii_2_couples_produit.ensembles_couples import singleton_membre
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import membre_reunion_graphes
    va = _t(a)
    Sa = _seg(R, E_set, a)
    SaA = _Saa(R, E_set, a)
    # a∈{a}
    a_in_sing = N.modus_ponens(N.reflexivite(va),
                               equivalence_arriere(singleton_membre(va, va)))
    car = membre_reunion_graphes(Sa, E.singleton(va), va)   # a∈Sa∪{a} ⇔ (a∈Sa ou a∈{a})
    return N.modus_ponens(
        N.modus_ponens(a_in_sing, N.s2(appartient(va, E.singleton(va)), appartient(va, Sa))),
        syllogisme(N.s3(appartient(va, E.singleton(va)), appartient(va, Sa)),
                   equivalence_arriere(car)))               # a∈]←,a]


def _coeur_temoin_concret(E_set, R, F_set, Rp, vu, vv, vS, vT, vphi):
    """Le CŒUR (8 conjoints) du témoin de h pour des TERMES concrets (S,T,φ),
    MIROIR EXACT de TS._h_parts / couple_iso_dans_h (binders « px »/« pw ») :

        est_segment(S,R,E) et est_segment(T,Rp,F)
        et est_isomorphisme_ordre(φ,S,T,R,Rp) et u∈S et v=valeur(φ,u)
        et est_fonctionnel(φ) et dom(φ)=S et φ⊂S×T."""
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    coeur5 = et(et(et(et(
        E.est_segment(vS, Rf, vE),
        E.est_segment(vT, Rpf, vF)),
        V.est_isomorphisme_ordre(vphi, vS, vT, Rf, Rpf, "px", "pw")),
        appartient(vu, vS)),
        egal(vv, E.valeur(vphi, vu)))
    return et(et(et(coeur5,
        E.est_fonctionnel(vphi)),
        egal(E.dom(vphi), vS)),
        inclus(vphi, E.produit(vS, vT)))


def _dom_hplus_eq_Saa(E_set, R, F_set, Rp, a, b):
    """⊢ { dom h = seg(R,E,a) } ⊢ dom(h⁺) = ]←,a] = seg(R,E,a)∪{a}.   (theorie=22.)

    dom(h⁺)=dom(h∪{(a,b)})=dom h ∪ dom{(a,b)} (dom_reunion_graphes) ; dom{(a,b)}={a}
    (ADJ.dom_singleton_couple) ; sous dom h=seg(R,E,a) (Prop 1), réécriture Leibniz
    ⇒ dom(h⁺)=seg(R,E,a)∪{a}=]←,a].  DÉRIVE le RÉSIDU (9) de la donnée Prop 1."""
    from bourbaki.ensembles.fonctions.hors_ii_3.iii_3_recollement.ensembles_restriction_somme import dom_reunion_graphes
    va, vb = _t(a), _t(b)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    G = ADJ.graphe_point(va, vb)
    hplus = _hplus(E_set, R, F_set, Rp, a, b)
    Sa = _seg(R, E_set, a)
    SaA = _Saa(R, E_set, a)                                  # = reunion(seg(R,E,a), {a})
    domh, domG = E.dom(h), E.dom(G)
    Saglob = E.singleton(va)

    dr = dom_reunion_graphes(h, G)                           # dom(h∪G)=dom h ∪ dom G
    dsc = ADJ.dom_singleton_couple(a, b)                     # dom G = {a}
    # réécrire dom G → {a} :  dom h ∪ dom G  →  dom h ∪ {a}
    step1 = _leib(domG, Saglob, dsc,
                  lambda w: egal(E.dom(hplus), E.reunion(domh, w)), dr)   # dom h⁺ = dom h ∪ {a}
    # réécrire dom h → seg(R,E,a) :  dom h ∪ {a}  →  seg(R,E,a) ∪ {a}
    Hdom_eq = N.assume(egal(domh, Sa))                       # dom h = seg(R,E,a)
    step2 = _leib(domh, Sa, Hdom_eq,
                  lambda w: egal(E.dom(hplus), E.reunion(w, Saglob)), step1)  # dom h⁺ = seg∪{a}
    assert step2.conclusion == egal(E.dom(hplus), SaA)
    return step2                                             # dom(h⁺) = ]←,a]   [dom h=seg]


def couple_ab_dans_h_residu(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """⊢ { ── 4 RÉSIDU STRUCTUREL (précisément reportés, JAMAIS postulés) :
              (1) est_segment(]←,a], R, E)
              (2) est_segment(]←,b], Rp, F)
              (3) est_isomorphisme_ordre(h⁺, ]←,a], ]←,b], R, Rp)
              (10) h⁺ ⊂ ]←,a]×]←,b]
           ── + dom h = seg(R,E,a)  (DONNÉE Prop 1, fournit le RÉSIDU (9) dom h⁺=]←,a])
           ── + conjoints EXPLICITES déchargés depuis a,b sommets :  a∈E, b∈F
           ── + structurels HONNÊTES :  func h, a∉dom h }
          ⊢ ( a, b ) ∈ h.

    Le cœur de la contradiction de maximalité : si h⁺=h∪{(a,b)} est l'iso d'une
    APPLICATION de segments ]←,a]≅]←,b] (RÉSIDU 1,2,3,9,10), avec a∈]←,a] (PROUVÉ) et
    b=h⁺(a) (PROUVÉ sous func h, a∉dom h), alors (a,b)∈h.  On bâtit le corps de
    l'axiome de h aux TERMES-TÉMOINS concrets (]←,a], ]←,b], h⁺) — MIROIR de
    couple_iso_dans_h mais avec WITNESS CONCRET (couple_iso_dans_h garde S,T,φ
    GÉNÉRIQUES, inutilisable avec un témoin spécifique).

    PIÈCES DÉCHARGÉES (PROUVÉES, theorie=22) :
      • a∈]←,a]            ← _a_dans_Saa (a∈{a}) ;
      • b=valeur(h⁺,a)     ← ADJ.valeur_temoin_en_a_sous_a_hors (func h, a∉dom h) ;
      • est_fonctionnel(h⁺)← ADJ.temoin_fonctionnel_sous_a_hors (func h, a∉dom h).

    RÉSIDU 3 (l'iso w.r.t. R,Rp) est l'OBSTRUCTION PRÉCISE : extension_iso_depuis_iso_h
    (ensembles_trichotomie_extension_iso) fournit l'iso pour les ordres ADJOINTS
    ≤'_a/≤'_b, PAS pour R/Rp — le pont ≤'_a⇔R sur ]←,a] (via réflexivité + a sommet du
    bon ordre) est le maillon restant.  Reporté en hypothèse, JAMAIS postulé.

    ⚠️ v=b doit être GÉNÉRIQUE (variable) avec v=φ(u) explicite, pour éviter la capture
    du liant τy de valeur(h⁺,a) — exactement la convention de couple_iso_dans_h."""
    va, vb = _t(a), _t(b)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    hplus = _hplus(E_set, R, F_set, Rp, a, b)
    SaA = _Saa(R, E_set, a)
    TbB = _Tbb(Rp, F_set, b)
    Rf, Rpf = _R_de(R), _R_de(Rp)

    # ── 4 hypothèses RÉSIDU + dom-Prop1 + 2 explicites + valeur ──
    Hseg_S = N.assume(E.est_segment(SaA, Rf, vE))                  # (1)
    Hseg_T = N.assume(E.est_segment(TbB, Rpf, vF))                 # (2)
    Hiso = N.assume(V.est_isomorphisme_ordre(hplus, SaA, TbB, Rf, Rpf, "px", "pw"))  # (3)
    # (9) dom(h⁺)=]←,a] DÉRIVÉ de dom h = seg(R,E,a) (DONNÉE Prop 1, _dom_hplus_eq_Saa)
    Hdom = _dom_hplus_eq_Saa(E_set, R, F_set, Rp, a, b)           # dom h⁺=]←,a]  [dom h=seg(R,E,a)]
    Hgraph = N.assume(inclus(hplus, E.produit(SaA, TbB)))          # (10)
    Ha_E = N.assume(appartient(va, vE))                            # a∈E
    Hb_F = N.assume(appartient(vb, vF))                            # b∈F

    # ── PIÈCES PROUVÉES ──
    Hu_S = _a_dans_Saa(R, E_set, a)                                # a∈]←,a]
    val_eq = ADJ.valeur_temoin_en_a_sous_a_hors(E_set, R, F_set, Rp, a, b)  # h⁺(a)=b [func h, a∉dom h]
    Hveq = N.modus_ponens(val_eq, symetrie(E.valeur(hplus, va), vb))        # b=valeur(h⁺,a)
    Hfunc = ADJ.temoin_fonctionnel_sous_a_hors(E_set, R, F_set, Rp, a, b)   # func h⁺ [func h, a∉dom h]

    # ── construire le cœur (8 conjoints) puis introduire ∃S,∃T,∃φ aux TÉMOINS ──
    preuve_coeur5 = conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(Hseg_S, Hseg_T), Hiso), Hu_S), Hveq)
    preuve_coeur = conjonction_intro(conjonction_intro(conjonction_intro(
        preuve_coeur5, Hfunc), Hdom), Hgraph)

    body_phi = _coeur_temoin_concret(E_set, R, F_set, Rp, va, vb, SaA, TbB, var("phi"))
    ex_phi = N.modus_ponens(preuve_coeur, N.s5(body_phi, hplus, "phi"))
    body_T = existe("phi", _coeur_temoin_concret(E_set, R, F_set, Rp, va, vb, SaA, var("T"), var("phi")))
    ex_T = N.modus_ponens(ex_phi, N.s5(body_T, TbB, "T"))
    body_S = existe("T", existe("phi",
        _coeur_temoin_concret(E_set, R, F_set, Rp, va, vb, var("S"), var("T"), var("phi"))))
    ex_S = N.modus_ponens(ex_T, N.s5(body_S, SaA, "S"))

    corps = conjonction_intro(conjonction_intro(Ha_E, Hb_F), ex_S)
    return N.modus_ponens(corps, equivalence_arriere(
        TS.h_membre(E_set, R, F_set, Rp, va, vb)))                 # (a,b)∈h


def couple_ab_dans_h_residu_cible(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """ÉNONCÉ-cible (test miroir) :  (a,b) ∈ h."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    return appartient(E.couple(_t(a), _t(b)), h)


def couple_ab_dans_h_residu_hyps(E_set="E", R="R", F_set="F", Rp="Rp", a="a", b="b"):
    """Les 4 hypothèses RÉSIDU STRUCTUREL (documentation / test miroir).

    Le RÉSIDU (9) dom h⁺=]←,a] N'EST PLUS une hypothèse : il est DÉRIVÉ de
    dom h = seg(R,E,a) (donnée Prop 1) par _dom_hplus_eq_Saa."""
    va, vb = _t(a), _t(b)
    vE, vF = _t(E_set), _t(F_set)
    hplus = _hplus(E_set, R, F_set, Rp, a, b)
    SaA = _Saa(R, E_set, a)
    TbB = _Tbb(Rp, F_set, b)
    Rf, Rpf = _R_de(R), _R_de(Rp)
    return [
        E.est_segment(SaA, Rf, vE),
        E.est_segment(TbB, Rpf, vF),
        V.est_isomorphisme_ordre(hplus, SaA, TbB, Rf, Rpf, "px", "pw"),
        inclus(hplus, E.produit(SaA, TbB)),
    ]


# ════════════════════════════════════════════════════════════════════════════
#  helpers De Morgan / par l'absurde.
# ════════════════════════════════════════════════════════════════════════════
def _de_morgan_ou(thm_neg_ou):
    """De ⊢ ¬(A ∨ B) déduit (⊢ ¬A , ⊢ ¬B)."""
    A, B = thm_neg_ou.conclusion.sous[0].sous          # ¬(A∨B) → (A∨B) → (A,B)
    notA = _contrapose_mp(thm_neg_ou, N.s2(A, B))      # A ⇒ (A∨B)
    B_imp = syllogisme(N.s2(B, A), N.s3(B, A))         # B ⇒ (B∨A) ; (B∨A) ⇒ (A∨B)
    notB = _contrapose_mp(thm_neg_ou, B_imp)
    return notA, notB


def _contrapose_mp(thm_negC, thm_a_imp_c):
    """⊢ ¬C [thm_negC], ⊢ A⇒C ⟹ ⊢ ¬A   (contraposition + MP)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import contraposition
    return N.modus_ponens(thm_negC, contraposition(thm_a_imp_c))


def _par_absurde(thm_D_sous_negD, D):
    """De ⊢ D [hyp ¬D] (parmi d'autres hyps), déduit ⊢ D  (en DÉCHARGEANT ¬D).

    (¬D ⊢ D)  →  (¬D ⇒ D)  →  D  via  (¬¬D∨D)⇒(D∨D)⇒D  (dne + S1)."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import dne, mono_gauche
    imp = N.loi_deduction(non(D), thm_D_sous_negD)     # ¬D ⇒ D
    return N.modus_ponens(imp, syllogisme(mono_gauche(dne(D), D), N.s1(D)))


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 TARGET B — MAXIMALITÉ SUBSTANTIELLE : dom h = E  ou  pr₂ h = F (PROUVÉ).
# ════════════════════════════════════════════════════════════════════════════
def _prop1_temoin(R, e_set, d_term, w="w"):
    """De {bo(R,E), est_segment(D,R,E), D≠E} extrait (τ-témoin a*, faits) :

      a* := τx( est_plus_petit_element(R, E∖D, x) et D=seg(R,E,x) )
      ⊢ est_plus_petit_element(R, E∖D, a*) et D = seg(R,E,a*)     [3 hyps de prop1]

    Renvoie (a*, thm_paire) où thm_paire conclut la PAIRE au témoin canonique."""
    Rf = _R_de(R)
    ve, vd = _t(e_set), _t(d_term)
    DmD = E.difference(ve, vd)
    petit_x = et(appartient(var("x"), DmD),
                 pourtout(w, impl(appartient(var(w), DmD), Rf(var("x"), var(w)))))
    body_x = et(petit_x, egal(vd, _seg(R, e_set, var("x"))))
    from bourbaki.logique.i_1_termes_relations.formule import tau
    a_t = tau("x", body_x)
    # prop1 (3 hyps) ⊢ ∃x body_x
    p1 = P1.prop1_segment_propre(R, e_set, d_term, x="x", w=w)
    paire = N.modus_ponens(p1, N.existe_temoin(body_x, "x"))   # body_x[x:=a*]  [3 hyps]
    return a_t, paire


def maximalite_donne_trichotomie_prouve(E_set="E", R="R", F_set="F", Rp="Rp"):
    """🎯🎯 TARGET B.  ⊢ { bo(R,E), bo(Rp,F), residu_univ_app,
            ── + RÉSIDU back-and-forth (4 formules, au témoin a*=min(E∖dom h),
                  b*=min(F∖pr₂h)), précisément reportées :
              (1) est_segment(]←,a*], R, E)
              (2) est_segment(]←,b*], Rp, F)
              (3) est_isomorphisme_ordre(h⁺*, ]←,a*], ]←,b*], R, Rp)   ← GAP CŒUR
              (10) h⁺* ⊂ ]←,a*]×]←,b*]
            ── + est_segment(dom h, R, E), est_segment(pr₂ h, Rp, F) }
          ⊢ ( dom h = E )  ou  ( pr₂ h = F )   ( == maximalite_donne_trichotomie ).

    (Le RÉSIDU (9) dom h⁺*=]←,a*] est DÉRIVÉ — _dom_hplus_eq_Saa — de dom h=seg(R,E,a*),
     donnée par Prop 1 ; il N'EST PLUS une hypothèse.)

    🎯 Argument de MAXIMALITÉ (back-and-forth, magnitude Cantor–Bernstein).  PAR
    L'ABSURDE : supposons ¬(dom h=E ∨ pr₂h=F), i.e. dom h≠E ET pr₂h≠F.
      • dom h ⊂ E (h_dom_inclus_E) ; comme dom h segment PROPRE, Prop 1 §III.2
        (prop1_segment_propre) livre a*=min(E∖dom h) avec dom h = seg(R,E,a*) et,
        de a*∈E∖dom h (AXIOME_DIFF), a*∈E et a*∉dom h ;
      • symétriquement b*=min(F∖pr₂h), pr₂h=seg(Rp,F,b*), b*∈F, b*∉pr₂h ;
      • a*∉dom h donne, avec func h (PROUVÉE — TARGET A amont), les valeurs/fonctionnalité
        de h⁺* (ADJ.valeur_temoin/temoin_fonctionnel) ; sous le RÉSIDU (h⁺* iso de
        segments ]←,a*]≅]←,b*]), couple_ab_dans_h_residu donne (a*,b*)∈h ;
      • (a*,b*)∈h ⇒ a*∈dom h (couple_dans_h_donne_antecedent) — CONTREDIT a*∉dom h.
    Donc dom h=E ∨ pr₂h=F.

    Les SEULES hypothèses survivantes : {bo(R,E), bo(Rp,F), residu_univ_app} (HONNÊTES,
    via func h = fonctionnel_h_prouve) + les 2 SEGMENTS (dom h, pr₂ h) + le RÉSIDU
    back-and-forth (4 formules au témoin a*,b*).  theorie=22, rien postulé, NON vacueux.

    ⚠️ GAP PRÉCIS (RÉSIDU 3) : extension_iso_depuis_iso_h fournit l'iso de h⁺* pour les
    ordres ADJOINTS ≤'_a/≤'_b, PAS pour R/Rp — le pont ≤'⇔R sur le segment fermé
    (réflexivité + a* sommet du bon ordre) reste à fermer.  Reporté, JAMAIS postulé."""
    assert (E_set, R, F_set, Rp) == ("E", "R", "F", "Rp"), \
        "noms ambiants CANONIQUES requis (schéma coincidence_univ_app)"
    Rf, Rpf = _R_de(R), _R_de(Rp)
    vE, vF = _t(E_set), _t(F_set)
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    D = ou(egal(domh, vE), egal(imgh, vF))                 # la conclusion-cible

    Hneg = N.assume(non(D))                                # ¬(dom h=E ou pr₂h=F)
    not_dom_E, not_img_F = _de_morgan_ou(Hneg)             # dom h≠E , pr₂h≠F

    # ── func h PROUVÉE (sous {bo,bo,residu}) — amont de TARGET A ──
    func_h = MCP.fonctionnel_h_prouve(E_set, R, F_set, Rp)         # est_fonctionnel(h) [bo,bo,res]

    # ── Prop 1 côté dom : a* = min(E∖dom h), dom h = seg(R,E,a*) ──
    a_star, paire_a = _prop1_temoin(R, E_set, domh)        # paire_a : [bo(R,E), seg(dom h,R,E), dom h≠E]
    # DÉCHARGER dom h≠E par not_dom_E (porté par Hneg) ⇒ se replie dans Hneg
    paire_a = N.modus_ponens(not_dom_E,
        N.loi_deduction(non(egal(domh, vE)), paire_a))     # paire_a : [bo(R,E), seg(dom h,R,E), Hneg]
    petit_a = conjonction_elim_gauche(paire_a)             # est_plus_petit_element(R, E∖dom h, a*)
    dom_eq_seg = conjonction_elim_droite(paire_a)          # dom h = seg(R,E,a*)
    a_in_diff = conjonction_elim_gauche(petit_a)           # a*∈E∖dom h
    a_split = N.modus_ponens(a_in_diff,
        equivalence_avant(_diff_ssi(vE, domh, a_star)))    # a*∈E et ¬(a*∈dom h)
    a_in_E = conjonction_elim_gauche(a_split)              # a*∈E
    a_not_dom = conjonction_elim_droite(a_split)           # ¬(a*∈dom h)

    # ── Prop 1 côté img : b* = min(F∖pr₂h), pr₂h = seg(Rp,F,b*) ──
    b_star, paire_b = _prop1_temoin(Rp, F_set, imgh)       # paire_b : [bo(Rp,F), seg(pr₂h,Rp,F), pr₂h≠F]
    paire_b = N.modus_ponens(not_img_F,
        N.loi_deduction(non(egal(imgh, vF)), paire_b))     # paire_b : [bo(Rp,F), seg(pr₂h,Rp,F), Hneg]
    petit_b = conjonction_elim_gauche(paire_b)
    b_in_diff = conjonction_elim_gauche(petit_b)           # b*∈F∖pr₂h
    b_split = N.modus_ponens(b_in_diff,
        equivalence_avant(_diff_ssi(vF, imgh, b_star)))    # b*∈F et ¬(b*∈pr₂h)
    b_in_F = conjonction_elim_gauche(b_split)              # b*∈F

    # ── (a*,b*)∈h via couple_ab_dans_h_residu (au témoin a*,b*) ──
    couple_in_h = couple_ab_dans_h_residu(E_set, R, F_set, Rp, a_star, b_star)
    #   hyps : 4 RÉSIDU(a*,b*) + dom h=seg(R,E,a*) + a*∈E + b*∈F + func h + a*∉dom h
    # décharger dom h=seg(R,E,a*) par dom_eq_seg (Prop 1), a*∈E, b*∈F, func h, a*∉dom h
    couple_in_h = N.modus_ponens(dom_eq_seg,
        N.loi_deduction(egal(domh, _seg(R, E_set, a_star)), couple_in_h))    # déch. dom h=seg
    couple_in_h = N.modus_ponens(a_in_E, N.loi_deduction(appartient(a_star, vE), couple_in_h))
    couple_in_h = N.modus_ponens(b_in_F, N.loi_deduction(appartient(b_star, vF), couple_in_h))
    couple_in_h = N.modus_ponens(func_h, N.loi_deduction(E.est_fonctionnel(h), couple_in_h))
    couple_in_h = N.modus_ponens(a_not_dom,
        N.loi_deduction(non(appartient(a_star, domh)), couple_in_h))
    #   couple_in_h : (a*,b*)∈h  [4 RÉSIDU, bo×2, residu, segments + Hneg]

    # ── a*∈dom h, CONTREDIT a*∉dom h ──
    ab_in_h_form = appartient(E.couple(a_star, b_star), h)
    a_in_dom = MP.couple_dans_h_donne_antecedent(E_set, R, F_set, Rp, a_star, b_star)  # {(a*,b*)∈h}⊢a*∈dom h
    a_in_dom = N.modus_ponens(couple_in_h, N.loi_deduction(ab_in_h_form, a_in_dom))    # a*∈dom h
    # ex falso : a*∈dom h et ¬(a*∈dom h) ⇒ D
    D_falso = _ex_falso(a_in_dom, a_not_dom, D)            # D  [Hneg parmi hyps]
    return _par_absurde(D_falso, D)                       # D  (¬D déchargé)


def _diff_ssi(e, d, z):
    """⊢ ( z ∈ E∖D ) ⇔ ( z∈E et ¬(z∈D) ).   (AXIOME_DIFF instancié.)"""
    ve, vd, vz = _t(e), _t(d), _t(z)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, ve), vd), vz)


def maximalite_donne_trichotomie_prouve_cible(E_set="E", R="R", F_set="F", Rp="Rp"):
    """ÉNONCÉ-cible (test miroir) :  ( dom h = E ) ou ( pr₂ h = F )  ( == maximalite_donne_trichotomie )."""
    return M.maximalite_donne_trichotomie(E_set, R, F_set, Rp)


def maximalite_donne_trichotomie_prouve_residu(E_set="E", R="R", F_set="F", Rp="Rp"):
    """Le RÉSIDU back-and-forth (5 formules au témoin a*=min(E∖dom h), b*=min(F∖pr₂h)) —
    documentation / test miroir.  C'est le GAP PRÉCIS restant (cf. docstring)."""
    h = TS.h_iso_max(E_set, R, F_set, Rp)
    domh, imgh = E.dom(h), E.img(h)
    from bourbaki.logique.i_1_termes_relations.formule import tau
    Rf, Rpf = _R_de(R), _R_de(Rp)
    # τ-témoins a*, b* (mêmes que dans la preuve)
    def _tau(R_, e_, d_):
        ve, vd = _t(e_), _t(d_)
        DmD = E.difference(ve, vd)
        Rg = _R_de(R_)
        petit_x = et(appartient(var("x"), DmD),
                     pourtout("w", impl(appartient(var("w"), DmD), Rg(var("x"), var("w")))))
        body_x = et(petit_x, egal(vd, _seg(R_, e_, var("x"))))
        return tau("x", body_x)
    a_star = _tau(R, E_set, domh)
    b_star = _tau(Rp, F_set, imgh)
    return couple_ab_dans_h_residu_hyps(E_set, R, F_set, Rp, a_star, b_star)


__all__ = [
    # TARGET A
    "image_dom_egale_img", "image_dom_egale_img_cible",
    "h_est_iso_prouve", "h_est_iso_prouve_cible", "h_est_iso_prouve_hypotheses",
    # TARGET B — pièces
    "couple_ab_dans_h_residu", "couple_ab_dans_h_residu_cible",
    "couple_ab_dans_h_residu_hyps",
    # TARGET B — théorème
    "maximalite_donne_trichotomie_prouve",
    "maximalite_donne_trichotomie_prouve_cible",
    "maximalite_donne_trichotomie_prouve_residu",
]
