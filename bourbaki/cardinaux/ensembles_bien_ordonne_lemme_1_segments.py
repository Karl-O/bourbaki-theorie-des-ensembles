"""§III.2 — LEMME L1a (« segment minoré par son minimum ») : OSSATURE de
l'ISOMORPHISME D'ORDRE  t ↦ seg_ext(a,R,t)  d'un ensemble bien ordonné (a,R) sur
ses SEGMENTS PROPRES ordonnés par ⊂.

────────────────────────────────────────────────────────────────────────────────
RÔLE dans l'arc cardinaux_bien_ordonnes(a) → C61 → ℕ.

La voie R3 (route stratégique) réduit le verrou entier à `est_bien_ordonne(≤,[0,a])`,
dont la SEULE pièce de contenu est la clause de PLUS PETIT ÉLÉMENT.  La trichotomie /
comparaison des cardinaux ≤ a se fait PAR SEGMENTS : t↦seg(a,R,t) est un ISOMORPHISME
D'ORDRE de (a,R) sur la famille de ses segments propres, ordonnée par ⊂.  Ce module
fournit l'OSSATURE de cet isomorphisme, DÉCHARGÉE sur le SEUL bon ordre de (a,R).

Le VRAI segment initial strict d'extrémité t est (E.III.2.1)

    seg(a,R,t) := segment_extremite(R, a, t) = { u∈a | R{u,t} et u≠t },

caractérisé par AXIOME_SEGMENT_EXTREMITE (déjà dans theorie_ensembles=22, RIEN ajouté) :

    u ∈ seg(a,R,t)  ⇔  ( (u∈a et R{u,t}) et u≠t ).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (theorie=22, jamais postulé, jamais tautologie) :

  ✅ INCONDITIONNEL (sur le SEUL bon ordre de (a,R)) :

     • seg_strict_monotone_de_bon_ordre(R,a,t,s) :
          { est_bien_ordonne(R,a),  R{t,s} } ⊢ seg(a,R,t) ⊂ seg(a,R,s).
       La MONOTONIE (sens direct de l'iso) DÉCHARGÉE sur le bon ordre : un segment
       d'extrémité plus petite est inclus dans un segment d'extrémité plus grande.
       (Cœur = seg_strict_monotone de ensembles_segments_construction, SAIN ; ici on
       décharge transitif+antisym depuis est_bien_ordonne, on garde R{t,s}.)

     • segment_extremite_est_segment(R,a,t) :
          { est_bien_ordonne(R,a) } ⊢ est_segment(seg(a,R,t), R, a).
       🎯 INITIALITÉ — chaque seg(a,R,t) est un VRAI SEGMENT de (a,R) au sens de la
       Définition 2 (E.III.2.1) : seg(t)⊂a et (∀x,y)((x∈seg(t) et y∈a et y≤x) ⇒
       y∈seg(t)).  C'est le contenu « segment INITIAL » : seg(t) est clos vers le bas.
       DÉRIVÉE de transitivité + antisymétrie (vraies pour tout bon ordre).

  ⚠️ CONDITIONNEL — le sens RÉCIPROQUE de l'iso (order-reflecting), conditionné à la
     COMPARABILITÉ (totalité) de l'ordre, EXPLICITE en hypothèse :

     • seg_reflechit_ordre(R,a,t,s) :
          { ordre_antisymetrique(R),  comparables_dans(R,a,t,s),  t∈a }
              ⊢ seg(a,R,t) ⊂ seg(a,R,s) ⇒ R{t,s}.
       Le sens RÉCIPROQUE : si seg(t)⊂seg(s) alors t≤s.  Combiné à seg_strict_monotone
       il fait de t↦seg(t) un ISOMORPHISME D'ORDRE (équivalence seg(t)⊂seg(s) ⇔ R{t,s}
       sur les t≠s).  La COMPARABILITÉ (R{t,s} ou R{s,t}) est VRAIE pour tout bon ordre
       (un bon ordre est total) mais ce fait — application de la clause de plus petit
       élément à la paire {t,s} — est un lemme SÉPARÉ (L1b), d'où l'hypothèse explicite
       `comparables_dans`.  JAMAIS postulée comme théorème.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout est DÉRIVÉ de l'axiome de
segment (déjà présent) + propriétés d'ordre extraites de est_bien_ordonne.  🚫 jamais
tautologie / affaibli : aucune conclusion n'est l'une de ses hypothèses (transitivité +
antisymétrie sont RÉELLEMENT consommées).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus, ou,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import (
    a_implique_a, syllogisme, inclusion_reflexive,
)
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere, contraposition, dne,
)
from bourbaki.cardinaux.ensembles_segments_construction import (
    seg, membre_segment, seg_strict_monotone,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (R-as-function bourbakien)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ── petits utilitaires (autonomes, AUCUNE confiance nouvelle) ─────────────────
def _decharge(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


_HOLE = "hole_bo_l1"


def _leib_transport(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]  (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_falso(thm_a, thm_na, z):
    """Γ ⊢ A,  Δ ⊢ ¬A  ⟹  Γ∪Δ ⊢ Z.   (ex falso quodlibet : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.   ((P⇒¬P) ≡ (¬P∨¬P) → ¬P par S1.)"""
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)  # P⇒¬P = ¬P∨¬P
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))           # (¬P∨¬P)⇒¬P


def _proprietes_ordre_de_bon_ordre(R, a, mn=None, xn=None):
    """De est_bien_ordonne(R,a) extrait (h_trans, h_anti) et renvoie aussi la formule
    bo utilisée (pour partager exactement la même hypothèse).

    Si mn/xn fournis, les binders X,a,w internes de la clause de plus petit utilisent
    S,mn,xn (pour rester α-cohérent avec d'autres consommateurs)."""
    Rf = _R_de(R)
    va = _t(a)
    if mn is None:
        bo = E.est_bien_ordonne(Rf, va)
    else:
        bo = E.est_bien_ordonne(Rf, va, "x", "y", "z", "S", mn, xn)
    Hbo = N.assume(bo)                                  # est_bien_ordonne(R,a)
    ord_dans = conjonction_elim_gauche(Hbo)             # est_relation_ordre_dans(R,a)
    rel_ordre = conjonction_elim_gauche(ord_dans)       # est_relation_ordre(R)
    trans_anti = conjonction_elim_gauche(rel_ordre)     # transitif et antisym
    h_trans = conjonction_elim_gauche(trans_anti)       # ordre_transitif(R)
    h_anti = conjonction_elim_droite(trans_anti)        # ordre_antisymetrique(R)
    return h_trans, h_anti, bo


# ════════════════════════════════════════════════════════════════════════════
#  🎯 MONOTONIE de l'iso — DÉCHARGÉE sur le SEUL bon ordre de (a,R).
# ════════════════════════════════════════════════════════════════════════════
def seg_strict_monotone_de_bon_ordre(R="R", a="a", t="t", s="s"):
    """⊢ { est_bien_ordonne(R,a),  R{t,s} } ⊢ seg(a,R,t) ⊂ seg(a,R,s).

    🎯 LE SENS DIRECT de l'isomorphisme t↦seg(t), DÉCHARGÉ sur le bon ordre de (a,R) :
    transitivité + antisymétrie (les hypothèses d'ordre de seg_strict_monotone) sont
    EXTRAITES de est_bien_ordonne(R,a) ; il ne reste que R{t,s} (= l'ordre des indices).

    NON vacueux : la conclusion seg(t)⊂seg(s) n'est aucune hypothèse, et le cœur
    seg_strict_monotone consomme réellement transitivité + antisymétrie."""
    Rf = _R_de(R)
    h_trans, h_anti, _ = _proprietes_ordre_de_bon_ordre(R, a)
    mono = seg_strict_monotone(R, a, t, s)              # seg(t)⊂seg(s) [transitif, antisym, R{t,s}]
    mono = _decharge(mono, E.ordre_transitif(Rf), h_trans)
    mono = _decharge(mono, E.ordre_antisymetrique(Rf), h_anti)
    return mono                                         # [est_bien_ordonne(R,a), R{t,s}]


# ════════════════════════════════════════════════════════════════════════════
#  🎯 INITIALITÉ — chaque seg(a,R,t) est un SEGMENT de (a,R) (Définition 2).
#
#  est_segment(S,R,a) = S⊂a  et  (∀x,y)( (x∈S et y∈a et R{y,x}) ⇒ y∈S ).
#  Pour S = seg(t) = {u∈a | R{u,t} et u≠t} : clôture vers le bas via transitivité +
#  antisymétrie.  C'est le sens « segment INITIAL » de la correspondance.
# ════════════════════════════════════════════════════════════════════════════
def _inclus_seg_dans_a(R, a, t, z="z"):
    """⊢ seg(a,R,t) ⊂ a.   INCONDITIONNEL (1ʳᵉ composante de membre_segment).

    seg(t)⊂a = (∀z)(z∈seg(t) ⇒ z∈a).  De z∈seg(t), membre_segment donne
    ((z∈a et R{z,t}) et z≠t) → z∈a (double projection).

    ⚠️ binder « z » canonique (celui de `inclus`) pour que la conclusion coïncide
    LITTÉRALEMENT avec inclus(seg(t), a) — sinon mismatch de liant."""
    va = _t(a)
    vz = var(z)
    Hz = N.assume(appartient(vz, seg(R, a, t)))         # z∈seg(t)
    corps = N.modus_ponens(Hz, equivalence_avant(membre_segment(R, a, t, vz)))  # (z∈a et R{z,t}) et z≠t
    z_in_a = conjonction_elim_gauche(conjonction_elim_gauche(corps))            # z∈a
    body = N.loi_deduction(appartient(vz, seg(R, a, t)), z_in_a)                # z∈seg(t)⇒z∈a
    return N.generalisation(z, body)                    # (∀z)(z∈seg(t)⇒z∈a) = seg(t)⊂a


def segment_extremite_est_segment(R="R", a="a", t="t", x="x", y="y"):
    """⊢ { est_bien_ordonne(R,a) } ⊢ est_segment(seg(a,R,t), R, a).

    🎯 INITIALITÉ — le VRAI segment seg(a,R,t) EST un segment de (a,R) au sens de la
    Définition 2 (E.III.2.1) :  seg(t)⊂a  ET  (∀x,y)((x∈seg(t) et y∈a et y≤x)⇒y∈seg(t)).

    PREUVE (clôture vers le bas).  Soit x∈seg(t), y∈a, R{y,x}.
      x∈seg(t) ⇒ x∈a, R{x,t}, x≠t (membre_segment).
      • R{y,x} et R{x,t} ⇒ R{y,t}  (TRANSITIVITÉ).
      • y≠t : sinon y=t, donc R{y,x}=R{t,x} ; avec R{x,t} l'ANTISYMÉTRIE donne x=t,
        contredisant x≠t.
      Donc y∈a et R{y,t} et y≠t ⇒ y∈seg(t).
    SEULES hypothèses (après décharge) : est_bien_ordonne(R,a).  NON vacueux :
    transitivité + antisymétrie RÉELLEMENT utilisées ; la conclusion est_segment(…)
    n'est pas l'hypothèse."""
    Rf = _R_de(R)
    va, vt = _t(a), _t(t)
    vx, vy = var(x), var(y)
    St = seg(R, a, t)
    h_trans, h_anti, _ = _proprietes_ordre_de_bon_ordre(R, a)

    # ── 1ʳᵉ composante : seg(t) ⊂ a
    incl = _inclus_seg_dans_a(R, a, t)                  # ⊢ seg(t)⊂a  (inconditionnel)

    # ── 2ᵉ composante : (∀x,y)((x∈seg(t) et y∈a et R{y,x}) ⇒ y∈seg(t))
    #    (forme de est_segment : impl(et(et(x∈S, y∈a), R{y,x}), y∈S))
    premisse = et(et(appartient(vx, St), appartient(vy, va)), Rf(vy, vx))
    Hpre = N.assume(premisse)
    x_in_St = conjonction_elim_gauche(conjonction_elim_gauche(Hpre))   # x∈seg(t)
    y_in_a = conjonction_elim_droite(conjonction_elim_gauche(Hpre))    # y∈a
    Ryx = conjonction_elim_droite(Hpre)                                # R{y,x}
    # déballer x∈seg(t)
    corps_x = N.modus_ponens(x_in_St, equivalence_avant(membre_segment(R, a, t, vx)))
    x_in_a_Rxt = conjonction_elim_gauche(corps_x)                      # x∈a et R{x,t}
    Rxt = conjonction_elim_droite(x_in_a_Rxt)                          # R{x,t}
    x_ne_t = conjonction_elim_droite(corps_x)                          # x≠t
    # R{y,t} par transitivité : (R{y,x} et R{x,t}) ⇒ R{y,t}
    trans_yxt = instancie(instancie(instancie(h_trans, vy), vx), vt)   # (R{y,x} et R{x,t})⇒R{y,t}
    Ryt = N.modus_ponens(conjonction_intro(Ryx, Rxt), trans_yxt)       # R{y,t}
    # y≠t : par l'absurde — supposer y=t
    Hyt = N.assume(egal(vy, vt))                                       # y=t
    #   de R{y,x} et y=t : R{t,x}
    Rtx = _leib_transport(vy, vt, Hyt, lambda w: Rf(w, vx), Ryx)       # R{t,x}
    #   antisymétrie : (R{x,t} et R{t,x}) ⇒ x=t
    anti_xt = instancie(instancie(h_anti, vx), vt)                     # (R{x,t} et R{t,x})⇒x=t
    x_eq_t = N.modus_ponens(conjonction_intro(Rxt, Rtx), anti_xt)      # x=t
    #   contradiction avec x≠t → ¬(y=t)
    falso = _ex_falso(x_eq_t, x_ne_t, non(egal(vy, vt)))              # ¬(y=t) [Hyt, …]
    y_ne_t = _refute_self(N.loi_deduction(egal(vy, vt), falso))        # y≠t
    # assembler y∈seg(t) via membre_segment arrière
    corps_y = conjonction_intro(conjonction_intro(y_in_a, Ryt), y_ne_t)  # (y∈a et R{y,t}) et y≠t
    y_in_St = N.modus_ponens(corps_y, equivalence_arriere(membre_segment(R, a, t, vy)))  # y∈seg(t)
    body = N.loi_deduction(premisse, y_in_St)                          # premisse ⇒ y∈seg(t)
    clos_bas = N.generalisation(x, N.generalisation(y, body))          # (∀x)(∀y)(…⇒y∈seg(t))

    # ── est_segment(seg(t),R,a) = (seg(t)⊂a) et clôture-bas
    res = conjonction_intro(incl, clos_bas)
    # décharge transitif+antisym → ne dépend que de est_bien_ordonne(R,a)
    res = _decharge(res, E.ordre_transitif(Rf), h_trans)
    res = _decharge(res, E.ordre_antisymetrique(Rf), h_anti)
    return res


def segment_extremite_est_segment_cible(R="R", a="a", t="t", x="x", y="y"):
    """ÉNONCÉ de la conclusion de segment_extremite_est_segment (test miroir) :

        est_segment(seg(a,R,t), R, a)   [seg = segment_extremite ; binders x,y canoniques]."""
    return E.est_segment(seg(R, a, t), _R_de(R), _t(a), x, y)


# ════════════════════════════════════════════════════════════════════════════
#  ⚠️ RÉCIPROQUE (order-reflecting) — conditionné à la COMPARABILITÉ + s∈a.
#
#  Si seg(t)⊂seg(s) alors R{t,s}.  Les seuls ingrédients « non-ordre » sont la
#  COMPARABILITÉ de t et s (vraie pour tout bon ordre — un bon ordre est total) et
#  s∈a, posés en HYPOTHÈSES explicites (lemme L1b séparé pour la comparabilité).
# ════════════════════════════════════════════════════════════════════════════
def comparables_dans(R, a, t, s):
    """« t et s comparables » := R{t,s} ou R{s,t}.

    Pour un bon ordre c'est TOUJOURS vrai (totalité) — mais ce fait est un lemme
    séparé (application de la clause de plus petit élément à la paire {t,s})."""
    Rf = _R_de(R)
    return ou(Rf(_t(t), _t(s)), Rf(_t(s), _t(t)))


def seg_reflechit_ordre(R="R", a="a", t="t", s="s"):
    """⊢ { (R{t,s} ou R{s,t}),  s∈a } ⊢ ( seg(a,R,t) ⊂ seg(a,R,s) ) ⇒ R{t,s}.

    🎯 LE SENS RÉCIPROQUE de l'isomorphisme t↦seg(t) (order-reflecting).  Combiné à
    seg_strict_monotone (sens direct), il établit l'ÉQUIVALENCE seg(t)⊂seg(s) ⇔ R{t,s}
    (pour t≠s), i.e. t↦seg(t) est un ISOMORPHISME D'ORDRE sur ses segments propres.

    PREUVE.  Supposer seg(t)⊂seg(s).  Par comparabilité, R{t,s} ou R{s,t}.
      • Cas R{t,s} : conclu directement.
      • Cas R{s,t} : tiers exclu sur s=t.
          – si s=t : alors R{t,s} s'obtient de R{s,t} par transport de l'égalité
            (Leibniz : remplacer s par t dans le 1ᵉʳ argument, t par s dans le 2ᵉ).
          – si s≠t : alors (s∈a et R{s,t}) et s≠t ⇒ s∈seg(t) (membre_segment) ; or
            seg(t)⊂seg(s) donne s∈seg(s), i.e. (s∈a et R{s,s}) et s≠s, d'où s≠s ;
            avec s=s (réflexivité) c'est ABSURDE : ex falso ⇒ R{t,s}.
    SEULES hypothèses : comparabilité de t,s (totalité, lemme L1b) et s∈a.  NON vacueux :
    la comparabilité et l'inclusion sont réellement utilisées ; la conclusion R{t,s}
    n'est aucune hypothèse."""
    Rf = _R_de(R)
    va, vt, vs = _t(a), _t(t), _t(s)
    St, Ss = seg(R, a, vt), seg(R, a, vs)
    from bourbaki.logique.tactiques.tactiques_abrege2 import cas, tiers_exclu

    Hcmp = N.assume(comparables_dans(R, a, vt, vs))         # R{t,s} ou R{s,t}
    Hs_in_a = N.assume(appartient(vs, va))                  # s∈a
    Hincl = N.assume(inclus(St, Ss))                        # seg(t)⊂seg(s)  (gardé en hyp ici)

    but = Rf(vt, vs)                                        # R{t,s}

    # ── cas A : R{t,s} ⇒ R{t,s}
    brA = a_implique_a(but)                                 # R{t,s} ⇒ R{t,s}

    # ── cas B : R{s,t} ⇒ R{t,s}, par tiers exclu sur (s=t)
    Hst = N.assume(Rf(vs, vt))                              # R{s,t}  (antécédent du cas B)
    #   sous-cas B1 : s=t ⇒ R{t,s}
    Hseqt = N.assume(egal(vs, vt))                          # s=t
    #     transport R{s,t} → R{t,t} (remplacer s par t dans 1ᵉʳ argument)
    Rtt = _leib_transport(vs, vt, Hseqt, lambda w: Rf(w, vt), Hst)   # R{t,t}
    #     transport R{t,t} → R{t,s} (remplacer t par s dans 2ᵉ argument, via t=s)
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie as _sym
    Hteqs = N.modus_ponens(Hseqt, _sym(vs, vt))            # t=s   (de s=t)
    Rts_B1 = _leib_transport(vt, vs, Hteqs, lambda w: Rf(vt, w), Rtt)  # R{t,s}
    brB1 = N.loi_deduction(egal(vs, vt), Rts_B1)           # (s=t) ⇒ R{t,s}   [Hst]
    #   sous-cas B2 : s≠t ⇒ R{t,s}  (par l'absurde)
    Hsnet = N.assume(non(egal(vs, vt)))                    # s≠t
    #     s∈seg(t) : (s∈a et R{s,t}) et s≠t  (membre_segment arrière)
    corps_s_in_St = conjonction_intro(conjonction_intro(Hs_in_a, Hst), Hsnet)  # (s∈a et R{s,t}) et s≠t
    s_in_St = N.modus_ponens(corps_s_in_St,
                             equivalence_arriere(membre_segment(R, a, t, vs)))  # s∈seg(t)
    #     seg(t)⊂seg(s) ⇒ s∈seg(s)
    s_in_Ss = N.modus_ponens(s_in_St, instancie(Hincl, vs))   # s∈seg(s)
    #     déballer : (s∈a et R{s,s}) et s≠s → s≠s
    corps_s_in_Ss = N.modus_ponens(s_in_Ss, equivalence_avant(membre_segment(R, a, s, vs)))
    s_ne_s = conjonction_elim_droite(corps_s_in_Ss)        # s≠s
    #     contradiction avec s=s → ex falso : R{t,s}
    Rts_B2 = _ex_falso(N.reflexivite(vs), s_ne_s, but)     # R{t,s}  [Hst, Hsnet, Hincl, Hs_in_a]
    brB2 = N.loi_deduction(non(egal(vs, vt)), Rts_B2)      # (s≠t) ⇒ R{t,s}
    #   recombiner B1/B2 par tiers exclu sur (s=t)
    te = tiers_exclu(egal(vs, vt))                         # (s=t) ou (s≠t)
    Rts_B = cas(te, brB1, brB2)                            # R{t,s}  [Hst, Hincl, Hs_in_a]
    brB = N.loi_deduction(Rf(vs, vt), Rts_B)              # R{s,t} ⇒ R{t,s}

    # ── recombiner cas A / cas B par la comparabilité
    Rts = cas(Hcmp, brA, brB)                              # R{t,s}  [Hcmp, Hincl, Hs_in_a]
    # décharger l'inclusion → conclusion en implication
    res = N.loi_deduction(inclus(St, Ss), Rts)            # (seg(t)⊂seg(s)) ⇒ R{t,s}  [Hcmp, Hs_in_a]
    return res


def seg_reflechit_ordre_cible(R="R", a="a", t="t", s="s"):
    """ÉNONCÉ de la conclusion de seg_reflechit_ordre (test miroir) :

        ( seg(a,R,t) ⊂ seg(a,R,s) ) ⇒ R{t,s}."""
    Rf = _R_de(R)
    return impl(inclus(seg(R, a, t), seg(R, a, s)), Rf(_t(t), _t(s)))


__all__ = [
    "seg",
    "seg_strict_monotone_de_bon_ordre",
    "segment_extremite_est_segment",
    "segment_extremite_est_segment_cible",
    "comparables_dans",
    "seg_reflechit_ordre",
    "seg_reflechit_ordre_cible",
]
