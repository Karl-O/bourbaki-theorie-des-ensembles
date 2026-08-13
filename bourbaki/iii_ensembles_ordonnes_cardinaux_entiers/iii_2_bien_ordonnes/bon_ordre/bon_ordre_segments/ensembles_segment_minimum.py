"""§III.2.1 — Le segment du PLUS PETIT élément est VIDE.

────────────────────────────────────────────────────────────────────────────────
THÉORÈME `segment_du_plus_petit_est_vide` :

    { est_bien_ordonne(R, E),  est_plus_petit_element(R, E, α) }
        ⊢  seg(R, E, α) = ∅.

« Le segment initial ]←, α[ d'extrémité le plus petit élément α est vide. »  Aucun
u ne peut vérifier (u∈E et R{u,α} et u≠α) : car α est le plus petit (α minore E),
donc u∈E donne R{α,u} ; avec R{u,α} l'ANTISYMÉTRIE force u=α, ce qui contredit u≠α.
Le segment n'a donc aucun élément : seg(R,E,α) = ∅.

────────────────────────────────────────────────────────────────────────────────
CONVENTIONS (calquées sur `ensembles_segment_strict_propre`/`..lemme4_segments`).

Le VRAI segment initial strict d'extrémité t est (E.III.2.1)

    seg(R,E,t) := segment_extremite(R, E, t)  [R = le GRAPHE] = { u∈E | R{u,t} et u≠t },

caractérisé par AXIOME_SEGMENT_EXTREMITE (déjà dans theorie_ensembles=22, RIEN ajouté) :

    u ∈ seg(R,E,t)  ⇔  ( (u∈E et R{u,t}) et u≠t ).

R est porté comme GRAPHE : R{a,b} := (a,b)∈R = `_Rgraphe(R)(a,b)`, lecture LITTÉRALE
identique à ce que `seg`/`membre_segment` consomment, et identique au `_R_de` interne.
est_bien_ordonne et est_plus_petit_element reçoivent donc cette même relation-fonction.

────────────────────────────────────────────────────────────────────────────────
STRATÉGIE (primitives N.* uniquement ; type Theoreme opaque ; theorie=22).

1.  De est_plus_petit_element(R,E,α) :
      • α∈E                         (conjonction_elim_gauche)
      • (∀x)(x∈E ⇒ R{α,x})          (conjonction_elim_droite)  ← α minore E.
    De est_bien_ordonne(R,E) : antisymétrie ordre_antisymetrique(R) (extraction).

2.  (∀u) ¬(u∈S_α).  Soit u∈S_α ; membre_segment sens AVANT → ((u∈E et R{u,α}) et u≠α).
      Projeter u∈E, R{u,α}, u≠α.  α minore E + u∈E → R{α,u}.  Antisymétrie en (u,α) :
      (R{u,α} et R{α,u}) ⇒ u=α.  Contradiction avec u≠α → ex falso → ¬(u∈S_α).

3.  S_α = ∅ par extensionnalité A1 :
      • S_α ⊂ ∅ : de ¬(u∈S_α), S2 → (u∈S_α ⇒ u∈∅).
      • ∅ ⊂ S_α : ex falso depuis AXIOME_VIDE ¬(u∈∅)  (motif `vide_est_segment`).
      A1 instancié : (S_α⊂∅ et ∅⊂S_α) ⇒ S_α=∅.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout dérive de l'axiome de
segment + A1 + AXIOME_VIDE (déjà présents) et des hypothèses load-bearing.  🚫 jamais
tautologie : la conclusion seg(R,E,α)=∅ n'est aucune des deux hypothèses.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, equivalence_avant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import (
    seg, membre_segment,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _Rgraphe(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (R-as-function bourbakien),
    IDENTIQUE au `_R_de` de ensembles_segments_construction (même couple, même ∈)
    pour que R{a,b} coïncide LITTÉRALEMENT avec ce que `seg`/`membre_segment` lisent."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ── ex falso (local, autonome, AUCUNE confiance nouvelle) ─────────────────────
def _ex_falso(thm_a, thm_na, z):
    """Γ ⊢ A,  Δ ⊢ ¬A  ⟹  Γ∪Δ ⊢ Z.   (ex falso quodlibet : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.   ((P⇒¬P) ≡ (¬P∨¬P) → ¬P par S1.)"""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import antecedent_consequent
    _P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)  # P⇒¬P = ¬P∨¬P
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))           # (¬P∨¬P)⇒¬P


def _antisym_de_bo(Hbo):
    """Extrait ⊢ ordre_antisymetrique(R) de ⊢ est_bien_ordonne(R,E) [Hbo].

    est_bien_ordonne = ( est_relation_ordre_dans(R,E) et clause_plus_petit ) ;
    est_relation_ordre_dans = ( est_relation_ordre(R) et reflexif ) ;
    est_relation_ordre = ( (transitif et antisym) et reflexif_impl )."""
    ord_dans = conjonction_elim_gauche(Hbo)              # est_relation_ordre_dans(R,E)
    rel_ordre = conjonction_elim_gauche(ord_dans)        # est_relation_ordre(R)
    trans_anti = conjonction_elim_gauche(rel_ordre)      # transitif et antisym
    return conjonction_elim_droite(trans_anti)           # ordre_antisymetrique(R)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 §III.2.1 — seg(R,E,α) = ∅  pour α = plus petit élément de E.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.1 Rem.- | E III.16 L.21-22 | PDF p.119  (petit texte : si E bien ordonné non vide, S_x = (α, x( — cas limite x=α : seg(α)=∅ ; maillon technique)
def segment_du_plus_petit_est_vide(R="R", E_="E", alpha="alpha", u="z"):
    """⊢ { est_bien_ordonne(R,E),  est_plus_petit_element(R,E,α) } ⊢ seg(R,E,α) = ∅.

    🎯 Le segment initial ]←, α[ du PLUS PETIT élément α est VIDE (E.III.2.1).
    Aucun u : si u∈S_α alors u∈E, R{u,α}, u≠α ; or α minore E donc R{α,u} ;
    l'antisymétrie sur (R{u,α} et R{α,u}) force u=α, contredisant u≠α.

    Séquent : conclusion = seg(R,E,α)=∅, hypothèses = EXACTEMENT les deux énoncés
    « E bien ordonné » et « α plus petit de E » (jamais la conclusion, jamais
    d'hypothèse parasite).  NON vacueux : la conclusion n'est aucune hypothèse, et
    antisymétrie + minorant sont RÉELLEMENT consommés."""
    Rf = _Rgraphe(R)
    ve, va = _t(E_), _t(alpha)
    vu = var(u)
    Sa = seg(R, E_, va)                                          # seg(R,E,α)

    # ── Hypothèses (deux assume distincts → séquent à exactement 2 hypothèses) ─
    hyp_bo = E.est_bien_ordonne(Rf, ve)                         # est_bien_ordonne(R,E)
    hyp_pp = E.est_plus_petit_element(Rf, ve, va)               # est_plus_petit_element(R,E,α)
    Hbo = N.assume(hyp_bo)
    Hpp = N.assume(hyp_pp)
    anti = _antisym_de_bo(Hbo)                                  # ordre_antisymetrique(R)
    minore_E = conjonction_elim_droite(Hpp)                    # (∀x)(x∈E ⇒ R{α,x})

    # ── (∀u) ¬(u∈S_α) ─────────────────────────────────────────────────────────
    Hu = N.assume(appartient(vu, Sa))                          # u∈S_α  (déchargé)
    corps = N.modus_ponens(Hu, equivalence_avant(membre_segment(R, E_, va, vu)))
    u_in_E_Rua = conjonction_elim_gauche(corps)                # u∈E et R{u,α}
    u_in_E = conjonction_elim_gauche(u_in_E_Rua)               # u∈E
    Rua = conjonction_elim_droite(u_in_E_Rua)                  # R{u,α}
    u_ne_a = conjonction_elim_droite(corps)                    # u≠α
    # α minore E + u∈E → R{α,u}
    Rau = N.modus_ponens(u_in_E, instancie(minore_E, vu))      # R{α,u}
    # antisymétrie (u,α) : (R{u,α} et R{α,u}) ⇒ u=α
    anti_ua = instancie(instancie(anti, vu), va)               # (R{u,α} et R{α,u}) ⇒ u=α
    u_eq_a = N.modus_ponens(conjonction_intro(Rua, Rau), anti_ua)  # u=α
    # contradiction avec u≠α → ¬(u∈S_α)  (Hu déchargé)
    falso = _ex_falso(u_eq_a, u_ne_a, non(appartient(vu, Sa)))  # ¬(u∈S_α)  [Hu,…]
    not_u_in_Sa = _refute_self(N.loi_deduction(appartient(vu, Sa), falso))  # ¬(u∈S_α)

    # ── S_α ⊂ ∅ :  (u∈S_α ⇒ u∈∅) par S2 depuis ¬(u∈S_α) ──────────────────────
    u_in_Sa_imp_vide = N.modus_ponens(not_u_in_Sa,
        N.s2(not_u_in_Sa.conclusion, appartient(vu, E.VIDE)))  # u∈S_α ⇒ u∈∅
    Sa_inc_vide = N.generalisation(u, u_in_Sa_imp_vide)        # S_α ⊂ ∅

    # ── ∅ ⊂ S_α :  ex falso depuis AXIOME_VIDE ¬(u∈∅)  (motif vide_est_segment) ─
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)   # (∀z)¬(z∈∅)
    not_u_vide = instancie(ax_vide, vu)                        # ¬(u∈∅)
    u_in_vide_imp = N.modus_ponens(not_u_vide,
        N.s2(not_u_vide.conclusion, appartient(vu, Sa)))       # u∈∅ ⇒ u∈S_α
    vide_inc_Sa = N.generalisation(u, u_in_vide_imp)           # ∅ ⊂ S_α

    # ── A1 (extensionnalité) : (S_α⊂∅ et ∅⊂S_α) ⇒ S_α=∅ ──────────────────────
    a1 = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), Sa), E.VIDE)
    res = N.modus_ponens(conjonction_intro(Sa_inc_vide, vide_inc_Sa), a1)  # S_α=∅

    assert res.conclusion == egal(Sa, E.VIDE), "conclusion ≠ (seg(R,E,α)=∅)"
    # Forme implication fermée éventuelle (décharge des deux hypothèses) :
    #   return N.loi_deduction(hyp_bo, N.loi_deduction(hyp_pp, res))
    return res                                                  # seg(R,E,α)=∅


def segment_du_plus_petit_est_vide_cible(R="R", E_="E", alpha="alpha"):
    """ÉNONCÉ de la conclusion de segment_du_plus_petit_est_vide (test miroir) :

        seg(R,E,α) = ∅   [seg = segment_extremite]."""
    return egal(seg(R, E_, _t(alpha)), E.VIDE)


__all__ = [
    "segment_du_plus_petit_est_vide",
    "segment_du_plus_petit_est_vide_cible",
]
