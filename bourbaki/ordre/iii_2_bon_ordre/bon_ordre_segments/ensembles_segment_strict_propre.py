"""§III.2.1 — Proposition 2 (préliminaire « x ↦ S_x STRICTEMENT croissante ») :
le TÉMOIN qui certifie la STRICTITÉ de l'inclusion des segments initiaux.

────────────────────────────────────────────────────────────────────────────────
RÔLE.  La Proposition 2 affirme que x ↦ seg(a,R,x) est CROISSANTE pour ⊂.  La
monotonie LARGE (S_x ⊂ S_y dès que R{x,y}) est déjà close ailleurs
(`seg_strict_monotone_de_bon_ordre`, paquet lemme4_segments).  Pour la STRICTITÉ
(S_x ⊊ S_y quand x≠y) il faut un TÉMOIN d'écart : un élément de S_y hors de S_x.
Ce module fournit ce témoin, x lui-même :

    x ∈ S_y   (car x∈E, R{x,y}, x≠y)        ET        x ∉ S_x   (inconditionnel).

Le VRAI segment initial strict d'extrémité t est (E.III.2.1)

    seg(a,R,t) := segment_extremite(R, a, t) = { u∈a | R{u,t} et u≠t },

caractérisé par AXIOME_SEGMENT_EXTREMITE (déjà dans theorie_ensembles=22, RIEN ajouté) :

    u ∈ seg(a,R,t)  ⇔  ( (u∈a et R{u,t}) et u≠t ).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (theorie=22, jamais postulé, jamais tautologie) :

  ✅ INCONDITIONNEL :
     • element_hors_de_son_segment(R,E,x) :
            ⊢ ¬( x ∈ seg(R,E,x) ).                       (0 hypothèse, est_clos.)
       Aucun élément n'appartient à SON PROPRE segment : x∈S_x forcerait, par
       l'axiome de segment, x≠x — absurde par réflexivité de l'égalité.

  ✅ CONDITIONNEL (antécédents load-bearing UNIQUEMENT) :
     • seg_strict_propre(R,E,x,y) :
            { x∈E,  R{x,y},  x≠y } ⊢ ( x ∈ seg(R,E,y)  et  ¬( x ∈ seg(R,E,x) ) ).
       🎯 LE TÉMOIN de S_x ⊊ S_y : x est dans S_y (membre_segment arrière sur
       (x∈E et R{x,y}) et x≠y) mais hors de S_x (lemme précédent).  Combiné à la
       monotonie large S_x ⊂ S_y, ce témoin certifie l'inclusion STRICTE.
       est_relation_ordre(R) n'est PAS nécessaire pour cette forme (le témoin ne
       consomme que l'axiome de segment) : on ne le met donc PAS en hypothèse.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout dérive de l'axiome de
segment (déjà présent) + réflexivité de l'égalité.  🚫 jamais tautologie : aucune
conclusion n'est l'une de ses hypothèses.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, appartient,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.lemme4_segments.ensembles_segments_construction import (
    seg, membre_segment,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ── ex falso (local, autonome, AUCUNE confiance nouvelle) ─────────────────────
def _ex_falso(thm_a, thm_na, z):
    """Γ ⊢ A,  Δ ⊢ ¬A  ⟹  Γ∪Δ ⊢ Z.   (ex falso quodlibet : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.   ((P⇒¬P) ≡ (¬P∨¬P) → ¬P par S1.)"""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)  # P⇒¬P = ¬P∨¬P
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))           # (¬P∨¬P)⇒¬P


# ════════════════════════════════════════════════════════════════════════════
#  🎯 (L-a)  x ∉ seg(R,E,x)  —  INCONDITIONNEL.
# ════════════════════════════════════════════════════════════════════════════
def element_hors_de_son_segment(R="R", E_="E", x="x"):
    """⊢ ¬( x ∈ seg(R,E,x) ).   INCONDITIONNEL (0 hypothèse, est_clos).

    Aucun élément n'appartient à SON PROPRE segment initial.  En effet, l'axiome de
    segment instancié donne  x∈S_x ⇔ ((x∈E et R{x,x}) et x≠x) ; supposer x∈S_x
    projette x≠x, qui contredit x=x (réflexivité).  D'où ¬(x∈S_x).

    PREUVE.  membre_segment(R,E,x,x) : (x∈S_x) ⇔ ((x∈E et R{x,x}) et x≠x).
      Assume x∈S_x ; equivalence_avant + modus_ponens → ((x∈E et R{x,x}) et x≠x) ;
      conjonction_elim_droite → x≠x ; N.reflexivite(x) → x=x ; ex_falso (x≠x ∧ x=x)
      donne ⊥ d'où ¬(x=x) ; loi_deduction de (x∈S_x ⇒ ¬(x=x)) puis _refute_self…
      plus simplement : ex_falso vise directement ¬(x∈S_x), et _refute_self ferme.
    NON vacueux : la conclusion ¬(x∈S_x) n'est aucune hypothèse (il n'y en a pas)."""
    vx = _t(x)
    Sx = seg(R, E_, vx)                                  # seg(R,E,x)
    cible = non(appartient(vx, Sx))                     # ¬(x∈S_x)
    # axiome de segment instancié : (x∈S_x) ⇔ ((x∈E et R{x,x}) et x≠x)
    Hx = N.assume(appartient(vx, Sx))                   # x∈S_x  (déchargé à la fin)
    corps = N.modus_ponens(Hx, equivalence_avant(membre_segment(R, E_, vx, vx)))
    x_ne_x = conjonction_elim_droite(corps)             # x≠x = ¬(x=x)
    x_eq_x = N.reflexivite(vx)                          # x=x
    # ex falso : de x=x et ¬(x=x), conclure ¬(x∈S_x)
    falso = _ex_falso(x_eq_x, x_ne_x, cible)            # ¬(x∈S_x)  [x∈S_x]
    res = _refute_self(N.loi_deduction(appartient(vx, Sx), falso))  # ¬(x∈S_x)  (clos)
    assert res.conclusion == cible, "conclusion ≠ ¬(x∈S_x)"
    assert res.est_clos, "element_hors_de_son_segment doit être INCONDITIONNEL"
    return res


def element_hors_de_son_segment_cible(R="R", E_="E", x="x"):
    """ÉNONCÉ de la conclusion de element_hors_de_son_segment (test miroir) :

        ¬( x ∈ seg(R,E,x) )   [seg = segment_extremite]."""
    vx = _t(x)
    return non(appartient(vx, seg(R, E_, vx)))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 (L-b)  TÉMOIN de S_x ⊊ S_y :  x∈S_y  ET  x∉S_x.
# ════════════════════════════════════════════════════════════════════════════
def seg_strict_propre(R="R", E_="E", x="x", y="y"):
    """⊢ { x∈E,  R{x,y},  x≠y } ⊢ ( x ∈ seg(R,E,y)  et  ¬( x ∈ seg(R,E,x) ) ).

    🎯 LE TÉMOIN d'écart certifiant S_x ⊊ S_y (sachant S_x ⊂ S_y déjà clos).
      • x∈S_y : de (x∈E et R{x,y}) et x≠y, membre_segment(R,E,y,x) sens ARRIÈRE
        (equivalence_arriere + modus_ponens) donne x∈seg(R,E,y).
      • x∉S_x : c'est element_hors_de_son_segment (INCONDITIONNEL).
      conjonction_intro des deux.

    SEULES hypothèses : x∈E, R{x,y}, x≠y — exactement les antécédents load-bearing
    pour x∈S_y (est_relation_ordre(R) inutile ici, donc absent).  NON vacueux : la
    conclusion (x∈S_y et x∉S_x) n'est aucune hypothèse."""
    vx, vy = _t(x), _t(y)
    Sy = seg(R, E_, vy)                                  # seg(R,E,y)
    Sx = seg(R, E_, vx)                                  # seg(R,E,x)

    # ── composante x∈S_y : construire le corps ((x∈E et R{x,y}) et x≠y) ────────
    Hx_in_E = N.assume(appartient(vx, _t(E_)))           # x∈E
    HRxy = N.assume(_Rgraphe(R)(vx, vy))                 # R{x,y}
    Hx_ne_y = N.assume(non(egal(vx, vy)))                # x≠y
    corps_y = conjonction_intro(conjonction_intro(Hx_in_E, HRxy), Hx_ne_y)
    x_in_Sy = N.modus_ponens(corps_y,
                             equivalence_arriere(membre_segment(R, E_, vy, vx)))  # x∈S_y

    # ── composante x∉S_x : lemme inconditionnel ───────────────────────────────
    x_notin_Sx = element_hors_de_son_segment(R, E_, vx)  # ¬(x∈S_x)  (clos)

    # ── assembler le témoin ───────────────────────────────────────────────────
    res = conjonction_intro(x_in_Sy, x_notin_Sx)         # x∈S_y et ¬(x∈S_x)
    assert res.conclusion == et(appartient(vx, Sy), non(appartient(vx, Sx))), \
        "conclusion ≠ (x∈S_y et ¬(x∈S_x))"
    return res


def seg_strict_propre_cible(R="R", E_="E", x="x", y="y"):
    """ÉNONCÉ de la conclusion de seg_strict_propre (test miroir) :

        ( x ∈ seg(R,E,y)  et  ¬( x ∈ seg(R,E,x) ) )   [seg = segment_extremite]."""
    vx, vy = _t(x), _t(y)
    return et(appartient(vx, seg(R, E_, vy)),
              non(appartient(vx, seg(R, E_, vx))))


def _Rgraphe(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (R-as-function bourbakien),
    IDENTIQUE à `_R_de` de ensembles_segments_construction (même couple, même ∈)
    pour que R{x,y} coïncide LITTÉRALEMENT avec ce que `seg`/`membre_segment` lisent."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


__all__ = [
    "element_hors_de_son_segment",
    "element_hors_de_son_segment_cible",
    "seg_strict_propre",
    "seg_strict_propre_cible",
]
