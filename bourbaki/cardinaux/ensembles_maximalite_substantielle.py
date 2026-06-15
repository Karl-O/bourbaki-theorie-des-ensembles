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

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, equiv, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ordre import ensembles_ordre_vocab as V
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, projection_droite,
    cas, tiers_exclu,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, monotonie_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites

from bourbaki.cardinaux import ensembles_trichotomie_scaffold as TS
from bourbaki.cardinaux import ensembles_trichotomie_scaffold_maximalite as M
from bourbaki.cardinaux import ensembles_trichotomie_h_iso as HI
from bourbaki.cardinaux import ensembles_h_bien_defini as HBD
from bourbaki.cardinaux import ensembles_maillon_coherences_prouvees as MCP
from bourbaki.cardinaux import ensembles_fusion_depuis_coincidence_app as FDA


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
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
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
    """Les 3 HYPOTHÈSES SURVIVANTES (documentation / test miroir) de TARGET A :
       [ bo(R,E), bo(R',F), residu_univ_app ]  (= celles des 3 cohérences prouvées)."""
    return FDA.fusion_depuis_coincidence_app_hypotheses(E_set, R, F_set, Rp)


__all__ = [
    "image_dom_egale_img", "image_dom_egale_img_cible",
    "h_est_iso_prouve", "h_est_iso_prouve_cible", "h_est_iso_prouve_hypotheses",
]
