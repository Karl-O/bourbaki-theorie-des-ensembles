"""§III.2 + §III.4 — CONSTRUCTION ORDINALE : MONOTONIE INCONDITIONNELLE des
SEGMENTS INITIAUX RÉELS d'un ensemble bien ordonné, pour fermer `seg_monotone`
de l'arc cardinaux_bien_ordonnes → C61 → ℕ.

────────────────────────────────────────────────────────────────────────────────
LE MUR (rappel).  Le verrou final de l'arc ℕ est `cardinaux_bien_ordonnes(a)` ;
sa voie Zermelo (ensembles_clause_plus_petit*) le réduit à DEUX pièces ordinales,
isolées en hypothèses pour le segment OPAQUE seg(a,R,x)=seg_initial_card(a,R,x) :

  (1) hyp_surjection(a,R,S)    : (∀x)( x∈S ⇒ Card(seg(a,R,x)) = x ).
  (2) seg_monotone(a,R,S,T)    : (∀u,v)((u∈S et v∈S) ⇒ (T{u,v} ⇒ seg(a,R,u)⊂seg(a,R,v))).

────────────────────────────────────────────────────────────────────────────────
APPROCHE CORRIGÉE de la mission (le verrou, CASSÉ pour la monotonie).

Le blocage de l'ancien `seg_monotone` (report inconditionnel) tenait à ce que
seg_initial_card(a,R,x) était indexé par un CARDINAL x via un terme OPAQUE, sans
caractérisation de membre.  La CORRECTION : travailler avec les VRAIS segments
initiaux de (a,R), indexés par les ÉLÉMENTS t∈a :

    seg(a,R,t) := segment_extremite(R, a, t) = { u∈a | R{u,t} et u≠t }     (E.III.2.1)

caractérisé par AXIOME_SEGMENT_EXTREMITE (déjà dans theorie_ensembles=22, RIEN
ajouté) :

    u ∈ seg(a,R,t)  ⇔  ( (u∈a et R{u,t}) et u≠t ).

Pour CES segments la MONOTONIE est DIRECTE et INCONDITIONNELLE (pas de transfini,
pas de construction représentationnelle) :

  🎯 seg_strict_monotone(R,a,t,t') :
       { ordre_transitif(R), ordre_antisymetrique(R), R{t,t'} }
           ⊢ segment_extremite(R,a,t) ⊂ segment_extremite(R,a,t').

  PREUVE.  Soit u∈seg(a,R,t), i.e. u∈a et R{u,t} et u≠t.
    • R{u,t} et R{t,t'} ⇒ R{u,t'}  (TRANSITIVITÉ).
    • u≠t' : sinon u=t' donnerait R{t',t} (de R{u,t}) et R{t,t'}, d'où t=t'
      (ANTISYMÉTRIE) ; or R{t,t'} avec t=t'… non : on a R{t,t'} en hyp, et u=t'
      donnerait t'≠t requis ; on conclut u≠t' car u=t' ⇒ (avec R{u,t}=R{t',t} et
      R{t,t'}) t=t', PUIS u=t'=t contredit u≠t.  ✓
    Donc u∈a et R{u,t'} et u≠t' ⇒ u∈seg(a,R,t').

Les SEULES hypothèses sont des propriétés de l'ORDRE (transitivité, antisymétrie)
— VRAIES pour tout bon ordre (est_relation_ordre) — plus R{t,t'} (= T{t,t'}, l'ordre
des indices).  Donc, sous « (a,R) bien ordonné », seg_monotone des VRAIS segments est
INCONDITIONNEL.  C'est le contenu de l'isomorphisme d'ordre t ↦ seg(a,R,t).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ✅ INCONDITIONNEL :
     • membre_segment      : u∈seg ⇔ ((u∈a et R{u,t}) et u≠t)   (axiome instancié).
     • seg_strict_monotone : { transitif, antisym, R{t,t'} } ⊢ seg(t) ⊂ seg(t').
       🎯 LA MONOTONIE DES SEGMENTS — directe, non transfinie, NON vacueuse.
     • seg_monotone_reel   : (∀u,v)((u∈S et v∈S) ⇒ (T{u,v} ⇒ seg(u)⊂seg(v)))
       sous { (∀ paires) transitif/antisym de l'ordre R des indices } — la pièce (2)
       LITTÉRALEMENT pour les vrais segments, conditionnée aux SEULES propriétés
       d'ordre (vraies pour tout bon ordre).
     • seg_monotone_de_bon_ordre : décharge transitif+antisym depuis est_bien_ordonne(R,a)
       — alors seg_monotone_reel ne dépend QUE de est_bien_ordonne(R,a).

  ⚠️ REPORTÉ — précisément (hypothèse explicite, JAMAIS postulée) :
     • report_surjection_construction : hyp_surjection — Card(seg(a,R,t))=« indice ».
       Exige le passage élément↦cardinal (type d'ordre du segment), maillon
       ordinal↔cardinal proprement dit.  STRUCTURE fournie ci-dessous.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la monotonie est DÉRIVÉE de
l'axiome de segment (déjà présent) + propriétés d'ordre.  🚫 jamais tautologie, jamais
affaibli déguisé : la conclusion seg(t)⊂seg(t') n'est aucune des hypothèses.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal_bon_ordre import plus_petit_de_bon_ordre


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (R-as-function bourbakien)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


def seg(R, a, t):
    """seg(a,R,t) := segment_extremite(R, a, t) = { u∈a | R{u,t} et u≠t }   (E.III.2.1).

    Le VRAI segment initial strict d'extrémité t dans l'ensemble ordonné (a,R).
    Caractérisé par AXIOME_SEGMENT_EXTREMITE (theorie_ensembles=22, rien ajouté)."""
    return E.segment_extremite(_R_de(R), _t(a), _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  MEMBRE — caractérisation de l'appartenance à un segment (axiome instancié).
# ════════════════════════════════════════════════════════════════════════════
def membre_segment(R="R", a="a", t="t", u="u"):
    """⊢ ( u ∈ seg(a,R,t) ) ⇔ ( (u∈a et R{u,t}) et u≠t ).

    Instance de AXIOME_SEGMENT_EXTREMITE aux TERMES a,t,u.  INCONDITIONNEL.
    (Le graphe R est porté par R_de(R) ; le binder y de l'axiome devient u.)"""
    Rf = _R_de(R)
    th = E.theorie_segment_extremite(Rf)
    ax = N.axiome(th, E.axiome_segment_extremite(Rf))           # (∀E∀x∀y)( y∈S_x ⇔ ((y∈E et R{y,x}) et y≠x) )
    return instancie(instancie(instancie(ax, _t(a)), _t(t)), _t(u))


def _membre_avant(R, a, t, u, h_in):
    """De ⊢ u∈seg(a,R,t) [h_in] déduit ⊢ ( (u∈a et R{u,t}) et u≠t )."""
    return N.modus_ponens(h_in, equivalence_avant(membre_segment(R, a, t, u)))


def _membre_arriere(R, a, t, u, h_corps):
    """De ⊢ ( (u∈a et R{u,t}) et u≠t ) [h_corps] déduit ⊢ u∈seg(a,R,t)."""
    return N.modus_ponens(h_corps, equivalence_arriere(membre_segment(R, a, t, u)))


# ════════════════════════════════════════════════════════════════════════════
#  Outils d'ORDRE instanciés (transitivité, antisymétrie aux TERMES).
# ════════════════════════════════════════════════════════════════════════════
def _trans_inst(R, x, y, z, h_trans):
    """De ⊢ ordre_transitif(R) [h_trans] déduit ⊢ (R{x,y} et R{y,z}) ⇒ R{x,z}."""
    Rf = _R_de(R)
    return instancie(instancie(instancie(h_trans, _t(x)), _t(y)), _t(z))


def _antisym_inst(R, x, y, h_anti):
    """De ⊢ ordre_antisymetrique(R) [h_anti] déduit ⊢ (R{x,y} et R{y,x}) ⇒ x=y."""
    return instancie(instancie(h_anti, _t(x)), _t(y))


# ════════════════════════════════════════════════════════════════════════════
#  🎯 LA MONOTONIE DES SEGMENTS — directe, INCONDITIONNELLE.
# ════════════════════════════════════════════════════════════════════════════
def seg_strict_monotone(R="R", a="a", t="t", s="s", u="u"):
    """⊢ { ordre_transitif(R), ordre_antisymetrique(R), R{t,s} }
            ⊢ seg(a,R,t) ⊂ seg(a,R,s)            (s joue le rôle de t').

    🎯 MONOTONIE DES SEGMENTS INITIAUX — un segment d'extrémité plus petite est
    inclus dans un segment d'extrémité plus grande.  DIRECTE, non transfinie.

    PREUVE (binder canonique « u » de ⊂).  u∈seg(a,R,t) ⇒ u∈a et R{u,t} et u≠t.
      • R{u,t} et R{t,s} ⇒ R{u,s}  (transitivité).
      • u≠s : si u=s, alors de R{u,t} on a R{s,t} ; avec R{t,s} l'antisymétrie donne
        t=s ; or R{t,s} ne force pas t≠s, mais u=s et t=s ⇒ u=t, contredisant u≠t.
        Donc u≠s.
      D'où u∈a et R{u,s} et u≠s ⇒ u∈seg(a,R,s).
    SEULES hypothèses : transitif, antisym (propriétés d'ordre VRAIES pour tout bon
    ordre) et R{t,s} (= l'ordre des indices).  NON vacueux : la conclusion seg(t)⊂seg(s)
    n'est aucune hypothèse, et transitivité+antisymétrie sont RÉELLEMENT utilisées."""
    Rf = _R_de(R)
    va, vt, vs = _t(a), _t(t), _t(s)
    St, Ss = seg(R, a, t), seg(R, a, s)
    # binder canonique de l'inclusion (= « u » par défaut)
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    cible = inclus(St, Ss)
    un, _ = _peler_pourtout(cible)
    vu = var(un)
    # hypothèses d'ordre + R{t,s}
    Htrans = N.assume(E.ordre_transitif(Rf))                    # ordre_transitif(R)
    Hanti = N.assume(E.ordre_antisymetrique(Rf))               # ordre_antisymetrique(R)
    Hts = N.assume(Rf(vt, vs))                                 # R{t,s}
    # u∈seg(a,R,t)
    Hu = N.assume(appartient(vu, St))                          # u∈seg(a,R,t)
    corps_t = _membre_avant(R, a, t, vu, Hu)                   # (u∈a et R{u,t}) et u≠t
    u_in_a_and_Rut = conjonction_elim_gauche(corps_t)         # u∈a et R{u,t}
    u_in_a = conjonction_elim_gauche(u_in_a_and_Rut)          # u∈a
    Rut = conjonction_elim_droite(u_in_a_and_Rut)            # R{u,t}
    u_ne_t = conjonction_elim_droite(corps_t)                 # u≠t
    # R{u,s} via transitivité : (R{u,t} et R{t,s}) ⇒ R{u,s}
    trans_uts = _trans_inst(R, vu, vt, vs, Htrans)            # (R{u,t} et R{t,s}) ⇒ R{u,s}
    Rus = N.modus_ponens(conjonction_intro(Rut, Hts), trans_uts)  # R{u,s}
    # u≠s : par l'absurde — supposer u=s
    Hus = N.assume(egal(vu, vs))                              # u=s
    #   de R{u,t} et u=s, par Leibniz : R{s,t}
    Rst = _leib_transport(vu, vs, Hus, lambda w: Rf(w, vt), Rut)  # R{s,t}
    #   antisymétrie : (R{t,s} et R{s,t}) ⇒ t=s
    anti_ts = _antisym_inst(R, vt, vs, Hanti)                 # (R{t,s} et R{s,t}) ⇒ t=s
    t_eq_s = N.modus_ponens(conjonction_intro(Hts, Rst), anti_ts)  # t=s
    #   u=s et t=s ⇒ u=t  (transitivité de l'égalité : u=s, s=t)
    from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie as _sym, transitivite as _trans_eg
    s_eq_t = N.modus_ponens(t_eq_s, _sym(vt, vs))            # s=t   (de t=s)
    #   transitivite(u,s,t) : conclusion u=t, hyps {u=s, s=t} → décharger les deux
    u_eq_t = _trans_eg(vu, vs, vt)                          # u=t   [u=s, s=t]
    u_eq_t = N.modus_ponens(Hus, N.loi_deduction(egal(vu, vs), u_eq_t))
    u_eq_t = N.modus_ponens(s_eq_t, N.loi_deduction(egal(vs, vt), u_eq_t))  # u=t
    #   contradiction avec u≠t  → ¬(u=s)  (Hus déchargé)
    falso = _ex_falso(u_eq_t, u_ne_t, non(egal(vu, vs)))     # ¬(u=s)  [Hus, …]
    u_ne_s = _refute_self(N.loi_deduction(egal(vu, vs), falso))  # u≠s
    # assembler le corps : (u∈a et R{u,s}) et u≠s ⇒ u∈seg(a,R,s)
    corps_s = conjonction_intro(conjonction_intro(u_in_a, Rus), u_ne_s)
    u_in_Ss = _membre_arriere(R, a, s, vu, corps_s)          # u∈seg(a,R,s)
    body = N.loi_deduction(appartient(vu, St), u_in_Ss)      # u∈seg(t) ⇒ u∈seg(s)
    res = N.generalisation(un, body)                         # seg(t) ⊂ seg(s)
    assert res.conclusion == inclus(St, Ss), "conclusion ≠ seg(t)⊂seg(s)"
    return res


# ── Leibniz + ex falso (locaux, autonomes) ───────────────────────────────────
_HOLE = "hole_seg_construction"


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
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)  # P⇒¬P = ¬P∨¬P
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))           # (¬P∨¬P)⇒¬P


# ════════════════════════════════════════════════════════════════════════════
#  seg_monotone des VRAIS segments — la pièce (2) LITTÉRALE, conditionnée aux
#  SEULES propriétés d'ordre (vraies pour tout bon ordre).
# ════════════════════════════════════════════════════════════════════════════
def seg_monotone_reel(R="R", a="a", S="S", u="us", v="vs"):
    """⊢ { ordre_transitif(R), ordre_antisymetrique(R) }
            ⊢ (∀u)(∀v)( (u∈S et v∈S) ⇒ ( R{u,v} ⇒ seg(a,R,u) ⊂ seg(a,R,v) ) ).

    🎯 La pièce seg_monotone LITTÉRALE pour les VRAIS segments, avec T := l'ordre R
    des indices (T{u,v} = R{u,v}).  Conditionnée aux SEULES transitivité+antisymétrie
    de R — VRAIES pour tout bon ordre (cf. seg_monotone_de_bon_ordre).  Les hypothèses
    u∈S, v∈S ne sont PAS utilisées (la monotonie vaut pour tous t,t'∈a) ; on les
    conserve pour calquer la FORME exacte de seg_monotone.

    NON vacueux : la conclusion (∀u,v)(…⇒seg⊂seg) n'est aucune hypothèse, et le cœur
    seg_strict_monotone consomme réellement transitivité+antisymétrie."""
    Rf = _R_de(R)
    vS = _t(S)
    vu, vv = var(u), var(v)
    Htrans = N.assume(E.ordre_transitif(Rf))
    Hanti = N.assume(E.ordre_antisymetrique(Rf))
    # noyau : { transitif, antisym, R{u,v} } ⊢ seg(u) ⊂ seg(v)
    mono = seg_strict_monotone(R, a, vu, vv)                  # seg(u)⊂seg(v)  [transitif, antisym, R{u,v}]
    # décharger transitif et antisym par les hypothèses portées (les garder en hyp)
    mono = N.modus_ponens(Htrans, N.loi_deduction(E.ordre_transitif(Rf), mono))
    mono = N.modus_ponens(Hanti, N.loi_deduction(E.ordre_antisymetrique(Rf), mono))
    # mono : seg(u)⊂seg(v)  [transitif, antisym, R{u,v}]   (R{u,v} encore en hyp)
    inner = N.loi_deduction(Rf(vu, vv), mono)               # R{u,v} ⇒ seg(u)⊂seg(v)  [transitif, antisym]
    outer = N.loi_deduction(et(appartient(vu, vS), appartient(vv, vS)), inner)  # (u∈S et v∈S) ⇒ (R{u,v}⇒…)
    res = N.generalisation(u, N.generalisation(v, outer))
    return res


def seg_monotone_de_bon_ordre(R="R", a="a", S="S", u="us", v="vs"):
    """⊢ { est_bien_ordonne(R, a) }
            ⊢ (∀u)(∀v)( (u∈S et v∈S) ⇒ ( R{u,v} ⇒ seg(a,R,u) ⊂ seg(a,R,v) ) ).

    🎯 seg_monotone des VRAIS segments DÉCHARGÉ sur le SEUL bon ordre de (a,R) :
    est_bien_ordonne(R,a) entraîne est_relation_ordre_dans(R,a), d'où transitivité
    et antisymétrie de R, qui ferment seg_monotone_reel.  INCONDITIONNEL relativement
    au bon ordre — exactement ce que Zermelo garantit sur a.

    NON vacueux : extraction réelle de transitif/antisym puis monotonie utilisée."""
    Rf = _R_de(R)
    Hbo = N.assume(E.est_bien_ordonne(Rf, _t(a)))            # est_bien_ordonne(R,a)
    # est_bien_ordonne = ( est_relation_ordre_dans(R,a) et clause_plus_petit )
    ord_dans = conjonction_elim_gauche(Hbo)                  # est_relation_ordre_dans(R,a)
    rel_ordre = conjonction_elim_gauche(ord_dans)            # est_relation_ordre(R)
    # est_relation_ordre = ((transitif et antisym) et reflexif_impl)
    trans_anti = conjonction_elim_gauche(rel_ordre)          # transitif et antisym
    h_trans = conjonction_elim_gauche(trans_anti)            # ordre_transitif(R)
    h_anti = conjonction_elim_droite(trans_anti)             # ordre_antisymetrique(R)
    mono = seg_monotone_reel(R, a, S, u, v)                  # [transitif, antisym]
    mono = N.modus_ponens(h_trans, N.loi_deduction(E.ordre_transitif(Rf), mono))
    mono = N.modus_ponens(h_anti, N.loi_deduction(E.ordre_antisymetrique(Rf), mono))
    return mono                                             # [est_bien_ordonne(R,a)]


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 PONT — hyp_bon_ordre_seg pour les VRAIS segments : ⊂-MIN existe, sous le
#  SEUL bon ordre de (a,R).  C'est la pièce (2) littérale pour seg=segment_extremite.
#
#  S⊂a non vide ⟶ (bon ordre de a) plus petit élément m∈S (R-minimal) ⟶ pour x∈S,
#  R{m,x} et m,x∈a, donc seg(m)⊂seg(x) (seg_strict_monotone) : m indexe le ⊂-min.
# ════════════════════════════════════════════════════════════════════════════
def hyp_bon_ordre_seg_reel(R="R", a="a", S="S", m="ms", x="xs",
                           xo="x", yo="y", zo="z"):
    """⊢ { est_bien_ordonne(R, a),  S ⊂ a,  S ≠ ∅ }
            ⊢ (∃m)( m∈S et (∀x)( x∈S ⇒ seg(a,R,m) ⊂ seg(a,R,x) ) ).

    🎯🎯 LE ⊂-MINIMUM DES SEGMENTS RÉELS — la pièce hyp_bon_ordre_seg LITTÉRALE pour
    seg = segment_extremite (vrais segments initiaux), DÉRIVÉE INCONDITIONNELLEMENT du
    SEUL bon ordre de (a,R).  Le bon ordre de a fournit le plus petit élément m de S
    (engine plus_petit_de_bon_ordre, INCONDITIONNEL) ; pour tout x∈S on a R{m,x} (m
    minore S) et m,x∈a (S⊂a), donc seg(m)⊂seg(x) par seg_strict_monotone.  Donc seg(m)
    est le ⊂-min de {seg(x)|x∈S}, indexé par m∈S.

    NON vacueux : extraction du plus petit (engine) ET monotonie des segments RÉELLEMENT
    utilisées.  SEULES hypothèses : bon ordre de a, S⊂a, S≠∅.  theorie=22, rien postulé."""
    Rf = _R_de(R)
    va, vS = _t(a), _t(S)
    mn = m if isinstance(m, str) else m.nom
    xn = x if isinstance(x, str) else x.nom
    vm, vx = var(mn), var(xn)
    Sm, Sx = seg(R, a, vm), seg(R, a, vx)
    # ── propriétés d'ordre depuis est_bien_ordonne(R,a) — MÊMES binders que ceux
    #    produits par plus_petit_de_bon_ordre (xo,yo,zo / S,ms,xs) pour PARTAGER
    #    l'unique hypothèse est_bien_ordonne (sinon doublon α-équivalent).
    bo_form = E.est_bien_ordonne(Rf, va, xo, yo, zo, S, mn, xn)
    Hbo = N.assume(bo_form)                                  # est_bien_ordonne(R,a)
    ord_dans = conjonction_elim_gauche(Hbo)
    rel_ordre = conjonction_elim_gauche(ord_dans)
    trans_anti = conjonction_elim_gauche(rel_ordre)
    h_trans = conjonction_elim_gauche(trans_anti)            # ordre_transitif(R)
    h_anti = conjonction_elim_droite(trans_anti)             # ordre_antisymetrique(R)
    # ── ENGINE : { est_bien_ordonne(R,a), S⊂a, S≠∅ } ⊢ (∃m)(m∈S et (∀x)(x∈S ⇒ R{m,x}))
    pp = plus_petit_de_bon_ordre(Rf, va, S, xo, yo, zo, mn, xn)  # [3 hyps]  binders ms,xs
    # ── per-témoin m : (m∈S et (∀x)(x∈S ⇒ R{m,x}))
    corps_R = et(appartient(vm, vS),
                 pourtout(xn, impl(appartient(vx, vS), Rf(vm, vx))))
    Hwit = N.assume(corps_R)
    m_in_S = conjonction_elim_gauche(Hwit)                   # m∈S
    body_R = conjonction_elim_droite(Hwit)                   # (∀x)(x∈S ⇒ R{m,x})
    # ── S⊂a (hypothèse) pour relire m∈a, x∈a
    Hsub = N.assume(inclus(vS, va))                          # S⊂a
    m_in_a = N.modus_ponens(m_in_S, instancie(Hsub, vm))     # m∈a
    # per-x : x∈S ⊢ seg(m)⊂seg(x)
    Hx = N.assume(appartient(vx, vS))                       # x∈S
    Rmx = N.modus_ponens(Hx, instancie(body_R, vx))         # R{m,x}
    x_in_a = N.modus_ponens(Hx, instancie(Hsub, vx))        # x∈a
    # seg_strict_monotone(R,a,m,x) : { transitif, antisym, R{m,x} } ⊢ seg(m)⊂seg(x)
    mono = seg_strict_monotone(R, a, vm, vx)                # seg(m)⊂seg(x)  [3 hyps]
    mono = N.modus_ponens(h_trans, N.loi_deduction(E.ordre_transitif(Rf), mono))
    mono = N.modus_ponens(h_anti, N.loi_deduction(E.ordre_antisymetrique(Rf), mono))
    incl_mx = N.modus_ponens(Rmx, N.loi_deduction(Rf(vm, vx), mono))  # seg(m)⊂seg(x)
    body_seg_x = N.loi_deduction(appartient(vx, vS), incl_mx)  # x∈S ⇒ seg(m)⊂seg(x)
    body_seg = N.generalisation(xn, body_seg_x)             # (∀x)(x∈S ⇒ seg(m)⊂seg(x))
    corps_seg = conjonction_intro(m_in_S, body_seg)         # m∈S et (∀x∈S)seg(m)⊂seg(x)
    # ── introduire (∃m) [binder ms] : témoin m
    body_r = et(appartient(var(mn), vS),
        pourtout(xn, impl(appartient(vx, vS),
                          inclus(seg(R, a, var(mn)), seg(R, a, vx)))))
    but = existe(mn, body_r)                                # (∃m)(m∈S et (∀x∈S)seg(m)⊂seg(x))
    ex = N.modus_ponens(corps_seg, N.s5(body_r, vm, mn))    # but
    # ── éliminer le ∃m de l'engine
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
    wit_imp = N.loi_deduction(corps_R, ex)                  # corps_R ⇒ but
    ex_imp = existe_elimination(wit_imp, mn)                # (∃m)corps_R ⇒ but
    res = N.modus_ponens(pp, ex_imp)                        # but  [est_bien_ordonne(R,a), S⊂a, S≠∅]
    return res


def hyp_bon_ordre_seg_reel_cible(R="R", a="a", S="S", m="ms", x="xs"):
    """ÉNONCÉ de la conclusion de hyp_bon_ordre_seg_reel (pour les tests miroir) :

        (∃m)( m∈S et (∀x)( x∈S ⇒ seg(a,R,m) ⊂ seg(a,R,x) ) )   [seg = segment_extremite]."""
    vS = _t(S)
    vm, vx = var(m), var(x)
    return existe(m, et(appartient(vm, vS),
        pourtout(x, impl(appartient(vx, vS),
                         inclus(seg(R, a, vm), seg(R, a, vx))))))


# ════════════════════════════════════════════════════════════════════════════
#  REPORT PRÉCIS — la SEULE pièce restante : la surjectivité élément↦cardinal.
# ════════════════════════════════════════════════════════════════════════════
def report_surjection_construction(R="R", a="a", S="S", t="ts"):
    """ÉNONCÉ du report — la correspondance segment↦cardinal restante :

        (∀t)( t∈S ⇒ Card(seg(a,R,t)) = t ).

    ⚠️ NON PROUVÉ.  Pour les VRAIS segments seg(a,R,t)=segment_extremite, ceci exige
    le passage de l'ÉLÉMENT t∈a à son CARDINAL via le type d'ordre du segment (la
    bijection canonique de l'arc ordinal↔cardinal) — maillon non encore construit dans
    le projet.  HYPOTHÈSE explicite, JAMAIS postulée comme théorème.

    STRUCTURE pour fermer (chantier futur) : sur le bon ordre (a,R) de Zermelo, pour
    t∈a le segment seg(a,R,t) est lui-même bien ordonné (sous-ensemble d'un bon ordre) ;
    son type d'ordre est l'ORDINAL associé à t, et Card de ce segment est le cardinal de
    cet ordinal.  L'identification « indice t = Card(seg t) » vaut quand S est l'image de
    a par t↦Card(seg t).  Reste à construire cette image et la bijection — sous-système
    ordinal représentationnel."""
    from bourbaki.cardinaux.ensembles_cardinaux import cardinal
    vS = _t(S)
    vt = var(t)
    return pourtout(t, impl(appartient(vt, vS), egal(cardinal(seg(R, a, vt)), vt)))


__all__ = [
    "seg",
    "membre_segment",
    "seg_strict_monotone",
    "seg_monotone_reel",
    "seg_monotone_de_bon_ordre",
    "hyp_bon_ordre_seg_reel",
    "hyp_bon_ordre_seg_reel_cible",
    "report_surjection_construction",
]
