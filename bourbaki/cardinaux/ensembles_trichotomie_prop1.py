"""§III.2 — Proposition 1 (E.III.2.1) : tout segment PROPRE d'un bon ordre est un
intervalle ]←, a[ (= segment_extremite), où a = min(E∖D).

────────────────────────────────────────────────────────────────────────────────
ÉNONCÉ (forme utile à la maximalité de la trichotomie, Th3 §III.2, maillon (d.5)) :

    { est_bien_ordonne(R,E),  est_segment(D,R,E),  D ≠ E }
        ⊢ (∃x)( est_plus_petit_element(R, E∖D, x)  et  D = seg(R,E,x) ).

(« x = min(E∖D)  et  D = ]←, x[ ».)

────────────────────────────────────────────────────────────────────────────────
PREUVE (fidèle Bourbaki, par minimalité du complémentaire).

  0. E∖D ⊂ E (AXIOME_DIFF) et E∖D ≠ ∅ :
     • si E∖D = ∅, alors E ⊂ D (tout z∈E qui n'est pas dans D serait dans E∖D=∅),
       et comme D ⊂ E (est_segment), l'extensionnalité A1 donne D=E — contredit D≠E.
  1. plus_petit_de_bon_ordre(R, E, E∖D) livre a = min(E∖D) :
       a ∈ E∖D  et  (∀w)( w∈E∖D ⇒ R{a,w} ).   Donc a∈E et a∉D.
  2. D = seg(R,E,a) par DOUBLE INCLUSION (A1) :

     (⊂) y∈D ⇒ y∈seg(R,E,a) = (y∈E et R{y,a} et y≠a) :
        • y∈E car D⊂E.
        • y≠a car y∈D et a∉D.
        • R{y,a} : par TOTALITÉ du bon ordre, R{y,a} ou R{a,y} ; si R{a,y}, alors la
          clause de SEGMENT (y∈D, a∈E, R{a,y} ⇒ a∈D) donne a∈D — contredit a∉D.
          Donc R{y,a}.

     (⊃) y∈seg(R,E,a) ⇒ y∈D :  y∈E, R{y,a}, y≠a.
        • si y∉D, alors y∈E∖D, donc (a minore E∖D) R{a,y} ; avec R{y,a} et
          l'ANTISYMÉTRIE : a=y, contredisant y≠a.  Donc y∈D.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : AXIOME_DIFF, AXIOME_VIDE,
A1 (extensionnalité), AXIOME_SEGMENT_EXTREMITE sont DÉJÀ dans theorie_ensembles ou
dans la théorie dédiée du segment (motif déjà validé) ; la totalité est dérivée
(`bon_ordre_est_total`).  Non vacueux : la conclusion D=seg(R,E,a) n'est aucune
hypothèse.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, appartient, existe, pourtout, inclus, tau,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere, cas, tiers_exclu,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.cardinaux.ensembles_ordinal_cardinal_bon_ordre import (
    bon_ordre_donne_clause_plus_petit,
)
from bourbaki.cardinaux.ensembles_bien_ordonne_total import bon_ordre_est_total
from bourbaki.cardinaux.ensembles_segments_construction import seg


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (R-as-function bourbakien).

    IDENTIQUE à `_R_de` de ensembles_bien_ordonne_total / ensembles_segments_construction
    — pour PARTAGER l'unique hypothèse est_bien_ordonne(R,E) entre les engines."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ── helpers autonomes (aucune confiance nouvelle) ─────────────────────────────
_HOLE = "hole_prop1"


def _leib(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]  (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_falso(thm_a, thm_na, z):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z.  (ex falso quodlibet : ¬A ⇒ (A ⇒ Z), S2.)"""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.  ((P⇒¬P) ≡ (¬P∨¬P) → ¬P par S1.)"""
    from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


# ── AXIOME_DIFF instancié : z ∈ E∖D ⇔ (z∈E et ¬(z∈D)) ────────────────────────
def _diff_ssi(e, d, z):
    """⊢ ( z ∈ E∖D ) ⇔ ( z∈E et ¬(z∈D) ).   (AXIOME_DIFF instancié, theorie=22.)"""
    ve, vd, vz = _t(e), _t(d), _t(z)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)   # ∀x∀y∀z(z∈x∖y ⇔ (z∈x et ¬(z∈y)))
    return instancie(instancie(instancie(ax, ve), vd), vz)


# ── AXIOME_SEGMENT_EXTREMITE instancié : u ∈ seg(R,E,a) ⇔ ((u∈E et R{u,a}) et u≠a)
def _membre_seg(R, e, a, u):
    """⊢ ( u ∈ seg(R,E,a) ) ⇔ ( (u∈E et R{u,a}) et u≠a ).  (axiome de segment instancié.)"""
    Rf = _R_de(R)
    th = E.theorie_segment_extremite(Rf)
    ax = N.axiome(th, E.axiome_segment_extremite(Rf))
    return instancie(instancie(instancie(ax, _t(e)), _t(a)), _t(u))


# ════════════════════════════════════════════════════════════════════════════
#  E∖D ⊂ E   (AXIOME_DIFF, binder « z » canonique de inclus)
# ════════════════════════════════════════════════════════════════════════════
def _diff_inclus(e, d, z="z"):
    """⊢ (E∖D) ⊂ E   (INCONDITIONNEL, via AXIOME_DIFF)."""
    ve, vd = _t(e), _t(d)
    vz = var(z)
    Hz = N.assume(appartient(vz, E.difference(ve, vd)))          # z∈E∖D
    corps = N.modus_ponens(Hz, equivalence_avant(_diff_ssi(ve, vd, vz)))  # z∈E et ¬(z∈D)
    z_in_E = conjonction_elim_gauche(corps)                     # z∈E
    body = N.loi_deduction(appartient(vz, E.difference(ve, vd)), z_in_E)  # z∈E∖D ⇒ z∈E
    return N.generalisation(z, body)                            # (E∖D)⊂E


# ════════════════════════════════════════════════════════════════════════════
#  E∖D ≠ ∅   (sous est_segment(D,R,E) et D≠E)
# ════════════════════════════════════════════════════════════════════════════
def _diff_non_vide(R, e, d, z="z"):
    """⊢ { est_segment(D,R,E),  D≠E } ⊢ (E∖D) ≠ ∅.

    Si E∖D=∅ : tout z∈E est dans D (sinon z∈E∖D=∅), donc E⊂D ; avec D⊂E
    (est_segment) l'extensionnalité A1 donne D=E — contredit D≠E."""
    Rf = _R_de(R)
    ve, vd = _t(e), _t(d)
    vz = var(z)
    DmD = E.difference(ve, vd)                                  # E∖D

    # D ⊂ E  (1er conjoint de est_segment)
    Hseg = N.assume(E.est_segment(vd, Rf, ve))                  # est_segment(D,R,E)
    D_inc_E = conjonction_elim_gauche(Hseg)                     # D⊂E

    # sous l'hypothèse E∖D=∅, montrer E⊂D
    Hempty = N.assume(egal(DmD, E.VIDE))                        # E∖D = ∅
    Hz = N.assume(appartient(vz, ve))                           # z∈E
    # cas z∈D : OK
    HzD = N.assume(appartient(vz, vd))                          # z∈D
    br_in = N.loi_deduction(appartient(vz, vd), HzD)            # z∈D ⇒ z∈D
    # cas ¬(z∈D) : z∈E∖D=∅ → contradiction → z∈D (ex falso)
    HnzD = N.assume(non(appartient(vz, vd)))                    # ¬(z∈D)
    z_in_diff = N.modus_ponens(conjonction_intro(Hz, HnzD),
                               equivalence_arriere(_diff_ssi(ve, vd, vz)))  # z∈E∖D
    z_in_vide = _leib(DmD, E.VIDE, Hempty, lambda w: appartient(vz, w), z_in_diff)  # z∈∅
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)    # (∀z)¬(z∈∅)
    not_z_vide = instancie(ax_vide, vz)                        # ¬(z∈∅)
    z_in_D_falso = _ex_falso(z_in_vide, not_z_vide, appartient(vz, vd))   # z∈D
    br_out = N.loi_deduction(non(appartient(vz, vd)), z_in_D_falso)  # ¬(z∈D) ⇒ z∈D
    z_in_D = cas(tiers_exclu(appartient(vz, vd)), br_in, br_out)  # z∈D  [Hempty,Hz,...]
    body_E_inc_D = N.loi_deduction(appartient(vz, ve), z_in_D)  # z∈E ⇒ z∈D
    E_inc_D = N.generalisation(z, body_E_inc_D)                # E⊂D  [Hempty, est_segment? no]

    # A1 : (D⊂E et E⊂D) ⇒ D=E
    a1 = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), vd), ve)  # (D⊂E et E⊂D)⇒D=E
    D_eq_E = N.modus_ponens(conjonction_intro(D_inc_E, E_inc_D), a1)  # D=E  [Hempty, est_segment]

    # contradiction avec D≠E  → ¬(E∖D=∅)
    HneqDE = N.assume(non(egal(vd, ve)))                       # D≠E
    falso = _ex_falso(D_eq_E, HneqDE, non(egal(DmD, E.VIDE)))   # ¬(E∖D=∅)  [Hempty,...]
    return _refute_self(N.loi_deduction(egal(DmD, E.VIDE), falso))  # E∖D≠∅  [est_segment, D≠E]


# ════════════════════════════════════════════════════════════════════════════
#  cible (test miroir)
# ════════════════════════════════════════════════════════════════════════════
def cible_prop1(R="R", e="E", d="D", x="x"):
    """ÉNONCÉ-cible : (∃x)( est_plus_petit_element(R, E∖D, x) et D = seg(R,E,x) )."""
    Rf = _R_de(R)
    ve, vd = _t(e), _t(d)
    vx = var(x)
    DmD = E.difference(ve, vd)
    petit = E.est_plus_petit_element(Rf, DmD, vx, x="w")
    return existe(x, et(petit, egal(vd, seg(R, e, vx))))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 PROPOSITION 1 §III.2 — segment propre = ]←, min(E∖D)[.
# ════════════════════════════════════════════════════════════════════════════
def prop1_segment_propre(R="R", e="E", d="D", x="x", w="w"):
    """⊢ { est_bien_ordonne(R,E), est_segment(D,R,E), D≠E }
            ⊢ (∃x)( est_plus_petit_element(R, E∖D, x) et D = seg(R,E,x) ).

    🎯 Proposition 1 (E.III.2.1) : tout segment PROPRE d'un bon ordre est un
    intervalle ]←, a[ d'extrémité a = min(E∖D).  Maillon (d.5) de la maximalité de
    la trichotomie (Th3 §III.2).  theorie=22, rien postulé, non vacueux."""
    Rf = _R_de(R)
    ve, vd = _t(e), _t(d)
    DmD = E.difference(ve, vd)                                  # E∖D

    # ── 0. E∖D ⊂ E  et  E∖D ≠ ∅ ──────────────────────────────────────────────
    diff_inc = _diff_inclus(e, d)                              # E∖D ⊂ E   (0 hyp)
    diff_nv = _diff_non_vide(R, e, d)                         # E∖D ≠ ∅   [est_segment, D≠E]

    # ── 1. a = min(E∖D)  via la clause CANONIQUE de bon ordre instanciée à E∖D ─
    bo = E.est_bien_ordonne(Rf, ve)                           # est_bien_ordonne(R,E) CANONIQUE
    clause = N.modus_ponens(N.assume(bo), bon_ordre_donne_clause_plus_petit(Rf, e))
    inst = instancie(clause, DmD)                            # ((E∖D)⊂E et (E∖D)≠∅) ⇒ ∃a(...)
    pp = N.modus_ponens(conjonction_intro(diff_inc, diff_nv), inst)  # ∃a(a∈E∖D et ∀w...)

    # témoin a = plus petit de E∖D (témoin canonique τ)
    corps_pp = et(appartient(var("a"), DmD),
                  pourtout(w, impl(appartient(var(w), DmD), Rf(var("a"), var(w)))))
    a = tau("a", corps_pp)
    temoin = N.modus_ponens(pp, N.existe_temoin(corps_pp, "a"))  # corps_pp[a:=a*]
    a_in_diff = conjonction_elim_gauche(temoin)               # a∈E∖D
    a_minore = conjonction_elim_droite(temoin)               # (∀w)(w∈E∖D ⇒ R{a,w})

    # a∈E et ¬(a∈D)
    a_split = N.modus_ponens(a_in_diff, equivalence_avant(_diff_ssi(ve, vd, a)))  # a∈E et ¬(a∈D)
    a_in_E = conjonction_elim_gauche(a_split)                # a∈E
    a_not_D = conjonction_elim_droite(a_split)               # ¬(a∈D)

    # propriétés du bon ordre : totalité + antisymétrie (sous est_bien_ordonne(R,E))
    Hbo = N.assume(bo)
    total = bon_ordre_est_total(R, e)                        # (∀x∀y)(x∈E et y∈E ⇒ R{x,y} ou R{y,x})  [bo]
    # antisymétrie de R (extraite de est_bien_ordonne)
    ord_dans = conjonction_elim_gauche(Hbo)                  # est_relation_ordre_dans(R,E)
    rel_ordre = conjonction_elim_gauche(ord_dans)            # est_relation_ordre(R)
    trans_anti = conjonction_elim_gauche(rel_ordre)          # transitif et antisym
    h_anti = conjonction_elim_droite(trans_anti)             # ordre_antisymetrique(R)

    # segment : clause de clôture-bas (2ᵉ conjoint de est_segment)
    Hseg = N.assume(E.est_segment(vd, Rf, ve))               # est_segment(D,R,E)
    D_inc_E = conjonction_elim_gauche(Hseg)                  # D⊂E
    seg_clause = conjonction_elim_droite(Hseg)               # (∀p)(∀q)((p∈D et q∈E et R{q,p}) ⇒ q∈D)

    vy = var("z")   # élément générique — binder « z » canonique de inclus (pour A1)
    Sa = seg(R, e, a)                                        # seg(R,E,a) = ]←,a[

    # ════════════════════════════════════════════════════════════════════════
    #  (⊂)  D ⊂ seg(R,E,a)
    # ════════════════════════════════════════════════════════════════════════
    HyD = N.assume(appartient(vy, vd))                       # y∈D
    # y∈E (D⊂E)
    y_in_E = N.modus_ponens(HyD, instancie(D_inc_E, vy))     # y∈E
    # y≠a : y∈D, a∉D  → si y=a alors a∈D, contradiction
    Hya = N.assume(egal(vy, a))                              # y=a
    a_in_D_via = _leib(vy, a, Hya, lambda u: appartient(u, vd), HyD)  # a∈D
    falso_ya = _ex_falso(a_in_D_via, a_not_D, non(egal(vy, a)))  # ¬(y=a)  [Hya,...]
    y_ne_a = _refute_self(N.loi_deduction(egal(vy, a), falso_ya))  # y≠a
    # R{y,a} : totalité de (y,a) ; si R{a,y} alors segment(y∈D,a∈E,R{a,y})⇒a∈D contradiction
    total_ya = N.modus_ponens(conjonction_intro(y_in_E, a_in_E),
                              instancie(instancie(total, vy), a))  # R{y,a} ou R{a,y}
    #   branche R{y,a} : direct
    br_Rya = N.loi_deduction(Rf(vy, a), N.assume(Rf(vy, a)))  # R{y,a} ⇒ R{y,a}
    #   branche R{a,y} : contradiction ⇒ R{y,a} (ex falso)
    HRay = N.assume(Rf(a, vy))                              # R{a,y}
    #   clause de segment instanciée à (p:=y, q:=a) : ((y∈D et a∈E) et R{a,y}) ⇒ a∈D
    seg_inst = instancie(instancie(seg_clause, vy), a)      # ((y∈D et a∈E) et R{a,y}) ⇒ a∈D
    a_in_D2 = N.modus_ponens(conjonction_intro(conjonction_intro(HyD, a_in_E), HRay), seg_inst)  # a∈D
    falso_Ray = _ex_falso(a_in_D2, a_not_D, Rf(vy, a))     # R{y,a}  (ex falso : a∈D et ¬a∈D)
    br_Ray = N.loi_deduction(Rf(a, vy), falso_Ray)         # R{a,y} ⇒ R{y,a}
    Rya = cas(total_ya, br_Rya, br_Ray)                    # R{y,a}
    # corps de seg : ((y∈E et R{y,a}) et y≠a) ⇒ y∈seg(R,E,a)
    corps_seg = conjonction_intro(conjonction_intro(y_in_E, Rya), y_ne_a)
    y_in_Sa = N.modus_ponens(corps_seg, equivalence_arriere(_membre_seg(R, e, a, vy)))  # y∈seg
    fwd = N.loi_deduction(appartient(vy, vd), y_in_Sa)     # y∈D ⇒ y∈seg(R,E,a)
    incl_D_Sa = N.generalisation("z", fwd)                 # D ⊂ seg(R,E,a)

    # ════════════════════════════════════════════════════════════════════════
    #  (⊃)  seg(R,E,a) ⊂ D
    # ════════════════════════════════════════════════════════════════════════
    HySa = N.assume(appartient(vy, Sa))                    # y∈seg(R,E,a)
    y_corps = N.modus_ponens(HySa, equivalence_avant(_membre_seg(R, e, a, vy)))  # (y∈E et R{y,a}) et y≠a
    yE_Rya = conjonction_elim_gauche(y_corps)             # y∈E et R{y,a}
    y_in_E2 = conjonction_elim_gauche(yE_Rya)             # y∈E
    Rya2 = conjonction_elim_droite(yE_Rya)               # R{y,a}
    y_ne_a2 = conjonction_elim_droite(y_corps)           # y≠a
    # si y∉D : y∈E∖D ⇒ R{a,y} (a minore) ; avec R{y,a} + antisym : a=y ⇒ y=a contradiction
    HnyD = N.assume(non(appartient(vy, vd)))             # ¬(y∈D)
    y_in_diff = N.modus_ponens(conjonction_intro(y_in_E2, HnyD),
                               equivalence_arriere(_diff_ssi(ve, vd, vy)))  # y∈E∖D
    Ray2 = N.modus_ponens(y_in_diff, instancie(a_minore, vy))  # R{a,y}
    # antisym instanciée à (a,y) : (R{a,y} et R{y,a}) ⇒ a=y
    anti_ay = instancie(instancie(h_anti, a), vy)        # (R{a,y} et R{y,a}) ⇒ a=y
    a_eq_y = N.modus_ponens(conjonction_intro(Ray2, Rya2), anti_ay)  # a=y
    y_eq_a = N.modus_ponens(a_eq_y, symetrie(a, vy))     # y=a
    falso_yD = _ex_falso(y_eq_a, y_ne_a2, appartient(vy, vd))  # y∈D  (ex falso : y=a et y≠a)
    br_nyD = N.loi_deduction(non(appartient(vy, vd)), falso_yD)  # ¬(y∈D) ⇒ y∈D
    br_yD = N.loi_deduction(appartient(vy, vd), N.assume(appartient(vy, vd)))  # y∈D ⇒ y∈D
    y_in_D = cas(tiers_exclu(appartient(vy, vd)), br_yD, br_nyD)  # y∈D
    bwd = N.loi_deduction(appartient(vy, Sa), y_in_D)    # y∈seg ⇒ y∈D
    incl_Sa_D = N.generalisation("z", bwd)               # seg(R,E,a) ⊂ D

    # ── extensionnalité A1 : D = seg(R,E,a) ──────────────────────────────────
    a1 = instancie(instancie(N.axiome(E.theorie_ensembles(), E.A1), vd), Sa)  # (D⊂seg et seg⊂D)⇒D=seg
    D_eq_Sa = N.modus_ponens(conjonction_intro(incl_D_Sa, incl_Sa_D), a1)  # D = seg(R,E,a)

    # ── recoller est_plus_petit_element(R, E∖D, a) ───────────────────────────
    #   = a∈E∖D et (∀w)(w∈E∖D ⇒ R{a,w})   (binder « w », aligné sur la clause)
    petit_a = conjonction_intro(a_in_diff, a_minore)     # est_plus_petit_element(R,E∖D,a)
    paire_concl = conjonction_intro(petit_a, D_eq_Sa)    # petit et D=seg(R,E,a)

    # ── introduire (∃x) [binder x] : témoin a ────────────────────────────────
    petit_x = et(appartient(var(x), DmD),
                 pourtout(w, impl(appartient(var(w), DmD), Rf(var(x), var(w)))))
    body_x = et(petit_x, egal(vd, seg(R, e, var(x))))
    but = existe(x, body_x)
    ex = N.modus_ponens(paire_concl, N.s5(body_x, a, x))  # but
    return ex


def prop1_segment_propre_clos(R="R", e="E", d="D", x="x", w="w"):
    """Forme CLOSE (0 hypothèse) : décharge les 3 hypothèses canoniques.

    ⊢ ( est_bien_ordonne(R,E) et est_segment(D,R,E) et D≠E ) ⇒
        (∃x)( est_plus_petit_element(R, E∖D, x) et D = seg(R,E,x) )."""
    Rf = _R_de(R)
    ve, vd = _t(e), _t(d)
    thm = prop1_segment_propre(R, e, d, x, w)
    bo = E.est_bien_ordonne(Rf, ve)
    seg_h = E.est_segment(vd, Rf, ve)
    neq = non(egal(vd, ve))
    out = thm
    out = N.loi_deduction(bo, out)
    out = N.loi_deduction(seg_h, out)
    out = N.loi_deduction(neq, out)
    return out


__all__ = [
    "cible_prop1",
    "prop1_segment_propre",
    "prop1_segment_propre_clos",
]
