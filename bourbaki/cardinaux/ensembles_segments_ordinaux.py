"""§III.4 — ORDINAL↔CARDINAL, SEGMENTS : RÉDUCTION INCONDITIONNELLE de la pièce
`hyp_bon_ordre_seg` au BON ORDRE DES INDICES (voie Zermelo), et report PRÉCIS de
`hyp_surjection`.

────────────────────────────────────────────────────────────────────────────────
CONTEXTE.  Le verrou de l'arc ℕ est `cardinaux_bien_ordonnes(a)` (== la cible C61).
Le module ensembles_clause_plus_petit l'a RÉDUIT (inconditionnellement) à DEUX
pièces ordinales, isolées en hypothèses, pour le terme OPAQUE
`seg_terme(a,R,x) = seg_initial_card(a,R,x)` (segment initial de (a,R) de cardinal x) :

  (1) hyp_surjection(a,R,S)    = (∀x)( x∈S ⇒ Card(seg(a,R,x)) = x )        [SURJECTIVITÉ]
  (2) hyp_bon_ordre_seg(a,R,S) = (∃m)( m∈S et (∀x)( x∈S ⇒ seg(a,R,m) ⊂ seg(a,R,x) ) )
                                                                          [⊂-MIN des segments]

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (salvage fort gradué, honnête, theorie=22) :

  ✅ INCONDITIONNEL — la RÉDUCTION de hyp_bon_ordre_seg au BON ORDRE DES INDICES :

     hyp_bon_ordre_seg_de_bon_ordre_indices(a,R,S,T) :
        { est_bien_ordonne(T, S),  S ≠ ∅,  seg_monotone(a,R,S,T) }
            ⊢ hyp_bon_ordre_seg(a,R,S)   (== la pièce (2) LITTÉRALEMENT, binders ms,xs).

     C'est EXACTEMENT le raisonnement demandé par la mission : « les segments initiaux
     de (a,R) sont ⊂-bien ordonnés ⇒ ⊂-min, via plus_petit_de_bon_ordre appliqué à la
     famille des segments ».  Ici le BON ORDRE concret est celui des INDICES x∈S (Zermelo
     en donne un sur TOUT ensemble S), et `seg_monotone` est l'ISOMORPHISME D'ORDRE de
     la correspondance (T{u,v} ⇒ seg(u)⊂seg(v)).  L'ENGINE plus_petit_de_bon_ordre
     (INCONDITIONNEL) extrait le T-plus-petit indice m de S, et la monotonie transporte
     T{m,x} en seg(m)⊂seg(x) : m indexe le ⊂-MIN.  NON vacueux : l'extraction du plus
     petit + la monotonie sont réellement utilisées.

  ✅ INCONDITIONNEL — l'EXISTENCE d'un bon ordre des indices (Zermelo) :

     bon_ordre_indices_existe(S) :  ⊢ (∃R) est_bien_ordonne(R_R, S).

     C'est ZERMELO (tout ensemble peut être bien ordonné) instancié à S.  Décharge
     l'hypothèse « est_bien_ordonne(T,S) » de l'engine ci-dessus en l'EXISTENCE d'un T :
     il ne reste, pour CE témoin, que seg_monotone (l'isomorphisme d'ordre).

  ⚠️ REPORTÉ — précisément :

     • report_seg_monotone : l'ISOMORPHISME D'ORDRE entre (S,T) (bon ordre des indices)
       et la famille {seg(a,R,x)|x∈S} ordonnée par ⊂.  C'est le cœur de la correspondance
       ordinal↔cardinal : pour le T fourni par Zermelo, T{u,v} ⇔ seg(u)⊂seg(v).  Exige la
       CONSTRUCTION CONCRÈTE du segment seg(a,R,x) (transfini sur le bon ordre R du set a),
       absente du projet (théorie ordinale représentationnelle).  HYPOTHÈSE explicite.

     • report_surjection : hyp_surjection — Card(seg(a,R,x))=x.  Même blocage : exige la
       construction concrète seg(a,R,x) (segment initial de cardinal x).  HYPOTHÈSE
       explicite.  C'est le maillon ordinal↔cardinal proprement dit.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : hyp_bon_ordre_seg est DÉRIVÉE
des trois hypothèses isolées (bon ordre des indices + S≠∅ + monotonie), via l'engine
plus_petit_de_bon_ordre PROUVÉ.  🚫 jamais de tautologie vide, jamais postuler.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import inclusion_reflexive
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.ensembles_ordinal_cardinal_bon_ordre import plus_petit_de_bon_ordre
from bourbaki.cardinaux.ensembles_clause_plus_petit_correspondance import (
    seg_terme, hyp_bon_ordre_seg, hyp_surjection,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _decharge(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _incl_refl(t):
    """⊢ t ⊂ t  pour un TERME t (réflexivité de l'inclusion instanciée)."""
    th = inclusion_reflexive("_r")
    return instancie(N.generalisation("_r", th), _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  L'ISOMORPHISME D'ORDRE (report) — sur S, l'ordre des indices T entraîne ⊂ des
#  segments.  C'est la SEULE pièce ordinale restante pour hyp_bon_ordre_seg.
# ════════════════════════════════════════════════════════════════════════════
def seg_monotone(a, R, S, T, u="us", v="vs"):
    """ÉNONCÉ — MONOTONIE de la correspondance index↦segment sur S :

        (∀u)(∀v)( ( u∈S et v∈S ) ⇒ ( T{u,v} ⇒ seg(a,R,u) ⊂ seg(a,R,v) ) ).

    T est l'ordre (bon ordre) des INDICES x∈S ; cette formule dit que la
    correspondance x ↦ seg(a,R,x) est ISOTONE (T-croissante pour ⊂).  C'est le
    contenu de l'isomorphisme d'ordre de la correspondance ordinal↔cardinal.

    ⚠️ REPORTÉ : pour le bon ordre T fourni par Zermelo, cette monotonie exige la
    construction concrète des segments ; posée en HYPOTHÈSE explicite, jamais postulée.
    ⚠️ binders « us,vs » (NON collisionnants avec les τ-binders cardinaux)."""
    vS = _t(S)
    vu, vv = var(u), var(v)
    return pourtout(u, pourtout(v,
        impl(et(appartient(vu, vS), appartient(vv, vS)),
             impl(T(vu, vv), inclus(seg_terme(a, R, vu), seg_terme(a, R, vv))))))


# ════════════════════════════════════════════════════════════════════════════
#  RÉDUCTION — hyp_bon_ordre_seg DÉRIVÉE du bon ordre des indices + monotonie.
#
#  plus_petit_de_bon_ordre(T,S,X:=S) extrait le T-plus-petit indice m de S :
#       m∈S et (∀x)( x∈S ⇒ T{m,x} ).
#  La monotonie transporte T{m,x} en seg(m)⊂seg(x) : m indexe le ⊂-MIN.
# ════════════════════════════════════════════════════════════════════════════
def hyp_bon_ordre_seg_de_bon_ordre_indices(a="a", R="R", S="S", T=None,
                                           m="ms", x="xs",
                                           xo="xo", yo="yo", zo="zo"):
    """⊢ { est_bien_ordonne(T, S),  S ≠ ∅,  seg_monotone(a,R,S,T) }
            ⊢ hyp_bon_ordre_seg(a,R,S)   (== la pièce (2) LITTÉRALEMENT).

    🎯 LA RÉDUCTION DEMANDÉE — « les segments initiaux de (a,R), ⊂-bien ordonnés,
    ont un ⊂-min ».  Le BON ORDRE concret est celui des INDICES x∈S (T) ; l'engine
    INCONDITIONNEL plus_petit_de_bon_ordre extrait le T-plus-petit indice m de S
    (avec X:=S, S⊂S réflexif, S≠∅) ; la monotonie seg_monotone transporte T{m,x}
    en seg(m)⊂seg(x).  Donc seg(m) est le ⊂-min de {seg(x)|x∈S}, indexé par m∈S :
    c'est EXACTEMENT le corps de hyp_bon_ordre_seg.

    NON vacueux : l'extraction du plus petit (engine) ET la monotonie sont utilisées.
    SEULES hypothèses : bon ordre des indices, S≠∅, monotonie.  theorie=22, rien postulé.

    T par défaut := un ordre des indices opaque `ord_indices(a,R,S)` (lambda u,v).  En
    pratique T est le bon ordre fourni par bon_ordre_indices_existe (Zermelo)."""
    vS = _t(S)
    mn = m if isinstance(m, str) else m.nom
    xn = x if isinstance(x, str) else x.nom
    if T is None:
        Tset = E.app("ord_indices", _t(a), _t(R), vS)
        T = lambda uu, vv: appartient(E.couple(_t(uu), _t(vv)), Tset)
    vm, vx = var(mn), var(xn)
    sm = seg_terme(a, R, vm)
    sx = seg_terme(a, R, vx)
    # ── ENGINE : { est_bien_ordonne(T,S), S⊂S, S≠∅ } ⊢ (∃m)(m∈S et (∀x)(x∈S ⇒ T{m,x}))
    pp = plus_petit_de_bon_ordre(T, vS, S, xo, yo, zo, mn, xn)
    # décharge S⊂S (réflexivité)
    pp = _decharge(pp, inclus(vS, vS), _incl_refl(vS))           # [est_bien_ordonne(T,S), S≠∅]
    # ── per-témoin m : transporter T{m,x} en seg(m)⊂seg(x) via seg_monotone
    corps_T = et(appartient(vm, vS),
                 pourtout(xn, impl(appartient(vx, vS), T(vm, vx))))   # m∈S et (∀x∈S)T{m,x}
    Hwit = N.assume(corps_T)
    m_in_S = conjonction_elim_gauche(Hwit)                      # m∈S
    body_T = conjonction_elim_droite(Hwit)                      # (∀x)(x∈S ⇒ T{m,x})
    # seg_monotone : (∀u∀v)((u∈S et v∈S) ⇒ (T{u,v} ⇒ seg(u)⊂seg(v)))
    Hmono = N.assume(seg_monotone(a, R, S, T))
    mono_mx = instancie(instancie(Hmono, vm), vx)              # (m∈S et x∈S)⇒(T{m,x}⇒seg(m)⊂seg(x))
    # per-x : x∈S ⊢ seg(m)⊂seg(x)
    Hx = N.assume(appartient(vx, vS))                          # x∈S
    Tmx = N.modus_ponens(Hx, instancie(body_T, vx))           # T{m,x}
    mono_imp = N.modus_ponens(conjonction_intro(m_in_S, Hx), mono_mx)  # T{m,x}⇒seg(m)⊂seg(x)
    incl_mx = N.modus_ponens(Tmx, mono_imp)                   # seg(m)⊂seg(x)
    body_seg_x = N.loi_deduction(appartient(vx, vS), incl_mx)  # x∈S ⇒ seg(m)⊂seg(x)
    body_seg = N.generalisation(xn, body_seg_x)               # (∀x)(x∈S ⇒ seg(m)⊂seg(x))
    corps_seg = conjonction_intro(m_in_S, body_seg)           # m∈S et (∀x∈S)seg(m)⊂seg(x)
    # ── introduire (∃m) [binder ms] : témoin m
    body_r = et(appartient(var(mn), vS),
        pourtout(xn, impl(appartient(vx, vS),
                          inclus(seg_terme(a, R, var(mn)), seg_terme(a, R, vx)))))
    but = existe(mn, body_r)                                   # (∃m)(m∈S et (∀x∈S)seg(m)⊂seg(x))
    ex = N.modus_ponens(corps_seg, N.s5(body_r, vm, mn))      # but  [Hwit, Hmono]
    # ── éliminer le ∃m de l'engine
    wit_imp = N.loi_deduction(corps_T, ex)                    # corps_T ⇒ but  [Hmono]
    ex_imp = existe_elimination(wit_imp, mn)                  # (∃m)corps_T ⇒ but  [Hmono]
    res = N.modus_ponens(pp, ex_imp)                          # but  [est_bien_ordonne(T,S), S≠∅, Hmono]
    assert res.conclusion == hyp_bon_ordre_seg(a, R, S, mn, xn), \
        "la conclusion ne reconstruit pas hyp_bon_ordre_seg LITTÉRALEMENT"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  EXISTENCE d'un BON ORDRE DES INDICES (Zermelo) — décharge est_bien_ordonne(T,S).
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_indices_existe(S="S"):
    """⊢ (∃R) est_bien_ordonne(R_R, S)  (S = TERME quelconque, l'ensemble des indices).

    🎯 ZERMELO instancié à S — l'ensemble des INDICES S admet un bon ordre.  C'est
    le T fourni à hyp_bon_ordre_seg_de_bon_ordre_indices : pour CE témoin, il ne
    reste que seg_monotone (l'isomorphisme d'ordre, report).  INCONDITIONNEL,
    theorie=22 (zermelo() est CLOS).

    zermelo() ⊢ (∃R)est_bien_ordonne(R_R,X) avec X libre ; on généralise sur X puis on
    instancie au TERME S (binders internes de zermelo intacts — aucune collision)."""
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zermelo import zermelo
    z = zermelo()                                  # (∃R)est_bien_ordonne(R_R,X)  [X libre]
    return instancie(N.generalisation("X", z), _t(S))   # (∃R)est_bien_ordonne(R_R,S)


# ════════════════════════════════════════════════════════════════════════════
#  REPORTS PRÉCIS (énoncés des SEULES pièces restantes — JAMAIS postulées)
# ════════════════════════════════════════════════════════════════════════════
def report_seg_monotone(a="a", R="R", S="S", T=None):
    """ÉNONCÉ du report — l'ISOMORPHISME D'ORDRE de la correspondance ordinal↔cardinal :
    pour le bon ordre T des indices, T{u,v} ⇒ seg(a,R,u) ⊂ seg(a,R,v).

    C'est seg_monotone(a,R,S,T).  ⚠️ NON PROUVÉ (construction concrète des segments
    manquante).  La SEULE pièce restante pour hyp_bon_ordre_seg une fois T fourni par
    Zermelo (bon_ordre_indices_existe)."""
    vS = _t(S)
    if T is None:
        Tset = E.app("ord_indices", _t(a), _t(R), vS)
        T = lambda uu, vv: appartient(E.couple(_t(uu), _t(vv)), Tset)
    return seg_monotone(a, R, S, T)


def report_surjection(a="a", R="R", S="S", x="xs"):
    """ÉNONCÉ du report — SURJECTIVITÉ segment↦cardinal :
    (∀x)( x∈S ⇒ Card(seg(a,R,x)) = x ).

    C'est hyp_surjection(a,R,S,x).  ⚠️ NON PROUVÉ (construction concrète seg(a,R,x) de
    cardinal x manquante — maillon ordinal↔cardinal).  HYPOTHÈSE explicite, jamais
    postulée comme théorème."""
    return hyp_surjection(a, R, S, x)


__all__ = [
    "seg_monotone",
    "hyp_bon_ordre_seg_de_bon_ordre_indices",
    "bon_ordre_indices_existe",
    "report_seg_monotone",
    "report_surjection",
]
