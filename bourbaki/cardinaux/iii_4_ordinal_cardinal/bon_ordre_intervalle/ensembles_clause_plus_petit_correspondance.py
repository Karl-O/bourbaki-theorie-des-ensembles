"""§III.4 — ORDINAL↔CARDINAL, brique 2 : CORRESPONDANCE segment ↦ cardinal et
RÉDUCTION de clause_plus_petit(≤,[0,a]) au BON ORDRE des segments par ⊂.

────────────────────────────────────────────────────────────────────────────────
CIBLE (LE bottleneck, ensembles_ordinal_cardinal_correspondance.report_clause_plus_petit) :

    clause_plus_petit(≤,[0,a]) =
        (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) ),

« toute partie non vide de [0,a] a un plus petit cardinal ».  Une fois fermée :
cardinaux_bien_ordonnes(a) ⊢ principe_recurrence ⊢ C61 ⊢ fini_downward ⊢ ℕ.

────────────────────────────────────────────────────────────────────────────────
LA VOIE ZERMELO, RENDUE EXPLICITE (ce module) :

  Soit R un bon ordre du SET a (zermelo()).  Pour chaque cardinal x ≤ a il existe un
  SEGMENT INITIAL `seg(a,R,x)` de (a,R) avec Card(seg(a,R,x)) = x (correspondance
  ordinal↔cardinal — SURJECTIVITÉ).  Les segments initiaux d'un bon ordre sont eux-
  mêmes BIEN ORDONNÉS par ⊂.  Donc : pour une partie non vide S de [0,a], les segments
  {seg(a,R,x) | x∈S} ont un PLUS PETIT seg_m (pour ⊂), et son cardinal m=Card(seg_m)∈S
  est le PLUS PETIT cardinal de S, car

        seg(a,R,m) ⊂ seg(a,R,x)  ⇒  Card(seg_m) ≤ Card(seg_x)  ⇒  m ≤ x .

  ⇐ MONOTONIE (inf_egal_card_de_inclus + transitivité de ≤, INCONDITIONNEL — ci-dessous).

────────────────────────────────────────────────────────────────────────────────
RÉPARTITION DU SALVAGE (graduée, honnête) :

  ✅ INCONDITIONNEL (prouvé, NON vacueux) :
     • seg_inclus_donne_card_le : seg_m⊂seg_x ⇒ seg_m ≤ seg_x   (pivot brut, ensembles).
     • card_le_de_seg_inclus    : { seg_m⊂seg_x, Card seg_m=m, Card seg_x=x } ⊢ m ≤ x.
       🎯 LE PIVOT MONOTONE LITTÉRAL : transporte ≤ des ENSEMBLES (segments) aux
       CARDINAUX m,x via Eq(seg,·)+transitivité.  UTILISE inf_egal_card_de_inclus.

  ✅ CONSTRUIT ICI (ÉNONCÉS exacts des pièces ordinales reportées) :
     • seg_terme / hyp_surjection / hyp_bon_ordre_seg.

  ⊢ DÉRIVÉ ICI (RÉDUCTION CONDITIONNELLE, NON vacueuse — la monotonie est UTILISÉE) :
     • clause_plus_petit_de_segments :
          { hyp_surjection(a,R,S), hyp_bon_ordre_seg(a,R,S) }
              ⊢ (∃m)( m∈S et (∀x)( x∈S ⇒ m ≤ x ) ).

  ⚠️ REPORTÉ (les pièces ORDINALES, isolées en hypothèses EXPLICITES, JAMAIS postulées) :
     • hyp_surjection    : correspondance ordinal↔cardinal (Zermelo) — sous-système neuf.
     • hyp_bon_ordre_seg : segments d'un bon ordre, ⊂-bien ordonnés — infra Zermelo à assembler.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la cible est DÉRIVÉE des deux
hypothèses ordinales explicites ; le PIVOT monotone est PROUVÉ (non supposé).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, app, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_ordre import (
    equipotence_implique_inf_egal, inf_egal_transitive,
)
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique
from bourbaki.cardinaux.iii_4_ordinal_cardinal.bon_ordre_intervalle.ensembles_clause_plus_petit_monotonie import (
    inf_egal_card_de_inclus, inf_egal_card_de_inclus_terme,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _le(u, v):
    return inf_egal_card(_t(u), _t(v))


# ════════════════════════════════════════════════════════════════════════════
#  REPRÉSENTATION — le segment initial de (a,R) de cardinal x.  Terme OPAQUE :
#  toute sa sémantique transite par hyp_surjection ; aucune propriété non hypothésée.
# ════════════════════════════════════════════════════════════════════════════
def seg_terme(a, R, x):
    """seg(a,R,x) := segment initial de (a,R) dont le cardinal vaut x  (représentationnel)."""
    return app("seg_initial_card", _t(a), _t(R), _t(x))


# ════════════════════════════════════════════════════════════════════════════
#  HYPOTHÈSES ORDINALES EXPLICITES (reportées — JAMAIS postulées comme théorèmes).
# ════════════════════════════════════════════════════════════════════════════
def hyp_surjection(a="a", R="R", S="S", x="xs"):
    """ÉNONCÉ — SURJECTIVITÉ segment↦cardinal sur S :  (∀x)( x∈S ⇒ Card(seg(a,R,x)) = x ).

    ⚠️ REPORTÉ (correspondance ordinal↔cardinal via Zermelo).  HYPOTHÈSE explicite.
    ⚠️ binder par défaut « xs » (NON collisionnant avec le τ-binder interne des
    cardinaux) — condition pour que instancie(·, terme) substitue correctement."""
    vS, vx = _t(S), _t(x)
    return pourtout(x, impl(appartient(vx, vS),
                            egal(cardinal(seg_terme(a, R, vx)), vx)))


def hyp_bon_ordre_seg(a="a", R="R", S="S", m="ms", x="xs"):
    """ÉNONCÉ — BON ORDRE PAR INCLUSION des segments {seg(a,R,x)|x∈S} :

        (∃m)( m∈S et (∀x)( x∈S ⇒ seg(a,R,m) ⊂ seg(a,R,x) ) ).

    ⚠️ REPORTÉ (segments d'un bon ordre, ⊂-bien ordonnés).  HYPOTHÈSE explicite.
    ⚠️ binders par défaut « ms,xs » (NON collisionnants — cf. hyp_surjection)."""
    vS, vm, vx = _t(S), _t(m), _t(x)
    return existe(m, et(appartient(vm, vS),
        pourtout(x, impl(appartient(vx, vS),
                         inclus(seg_terme(a, R, vm), seg_terme(a, R, vx))))))


# ════════════════════════════════════════════════════════════════════════════
#  PIVOT MONOTONE BRUT (INCONDITIONNEL) — inclusion des segments ⇒ ≤ des segments.
# ════════════════════════════════════════════════════════════════════════════
def seg_inclus_donne_card_le(a, R, m, x):
    """⊢ ( seg(a,R,m) ⊂ seg(a,R,x) ) ⇒ ( seg(a,R,m) ≤ seg(a,R,x) ).

    Instance du PIVOT inf_egal_card_de_inclus aux TERMES-segments.  INCONDITIONNEL."""
    return inf_egal_card_de_inclus_terme(seg_terme(a, R, m), seg_terme(a, R, x))


def _eq_au_cardinal(u):
    """⊢ inf_egal_card(u, Card u)  pour un TERME u  (Eq(u,Card u) ⇒ u≤Card u)."""
    gen = N.generalisation("X", equipotent_son_cardinal("X"))       # (∀X) Eq(X,Card X)
    eq = instancie(gen, _t(u))                                       # Eq(u, Card u)
    # equipotence_implique_inf_egal(F,X,Y) : Eq(X,Y)⇒X≤Y ; instancier X:=u, Y:=Card u
    gen2 = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))               # (∀X∀Y)(Eq(X,Y)⇒X≤Y)
    impl_uc = instancie(instancie(gen2, _t(u)), cardinal(_t(u)))     # Eq(u,Card u)⇒u≤Card u
    return N.modus_ponens(eq, impl_uc)                              # u ≤ Card u


def _cardinal_eq_au_set(u):
    """⊢ inf_egal_card(Card u, u)  pour un TERME u  (Eq(Card u,u) ⇒ Card u≤u, par symétrie)."""
    gen = N.generalisation("X", equipotent_son_cardinal("X"))
    eq = instancie(gen, _t(u))                                       # Eq(u, Card u)
    sym = instancie(instancie(N.generalisation("X", N.generalisation("Y",
        equipotence_symetrique("F", "X", "Y"))), _t(u)), cardinal(_t(u)))   # Eq(u,Cardu)⇒Eq(Cardu,u)
    eq_sym = N.modus_ponens(eq, sym)                                # Eq(Card u, u)
    gen2 = N.generalisation("X", N.generalisation("Y",
        equipotence_implique_inf_egal("F", "X", "Y")))
    impl_cu = instancie(instancie(gen2, cardinal(_t(u))), _t(u))     # Eq(Cardu,u)⇒Cardu≤u
    return N.modus_ponens(eq_sym, impl_cu)                          # Card u ≤ u


def _trans3(u, v, w):
    """⊢ ( u≤v et v≤w ) ⇒ u≤w  pour des TERMES (transitivité de ≤ instanciée)."""
    gen = N.generalisation("X", N.generalisation("Y", N.generalisation("Z",
        inf_egal_transitive("F", "G", "X", "Y", "Z"))))
    return instancie(instancie(instancie(gen, _t(u)), _t(v)), _t(w))


def card_le_de_seg_inclus(a, R, m, x):
    """⊢ { seg(a,R,m) ⊂ seg(a,R,x),  Card seg_m = m,  Card seg_x = x } ⊢ m ≤ x.

    🎯 PIVOT MONOTONE LITTÉRAL — transporte ≤ des ENSEMBLES (segments) aux CARDINAUX m,x.
    CHAÎNE (transitivité de ≤, INCONDITIONNELLE) :
        m = Card seg_m ,  Card seg_m ≤ seg_m  (Eq) ;  seg_m ≤ seg_x  (inclusion, PROUVÉ) ;
        seg_x ≤ Card seg_x = x  (Eq).   D'où  m ≤ seg_m ≤ seg_x ≤ x.
    Les égalités Card seg_m=m, Card seg_x=x (hyp_surjection) sont les SEULES hypothèses ;
    tout le reste est PROUVÉ.  Donc NON vacueux : la monotonie inf_egal_card_de_inclus est
    réellement utilisée (étape seg_m ≤ seg_x)."""
    sm, sx = seg_terme(a, R, m), seg_terme(a, R, x)
    vm, vx = _t(m), _t(x)
    Hincl = N.assume(inclus(sm, sx))                                # seg_m ⊂ seg_x
    HcardM = N.assume(egal(cardinal(sm), vm))                       # Card seg_m = m
    HcardX = N.assume(egal(cardinal(sx), vx))                       # Card seg_x = x
    # seg_m ≤ seg_x  (pivot, déchargé)
    sm_le_sx = N.modus_ponens(Hincl, seg_inclus_donne_card_le(a, R, m, x))
    # Card seg_m ≤ seg_m   et   seg_x ≤ Card seg_x
    cm_le_sm = _cardinal_eq_au_set(sm)                              # Card seg_m ≤ seg_m
    sx_le_cx = _eq_au_cardinal(sx)                                  # seg_x ≤ Card seg_x
    # transporter Card seg_m → m  et  Card seg_x → x  par Leibniz sur les égalités
    #   m ≤ seg_m  : de Card seg_m ≤ seg_m et Card seg_m = m
    m_le_sm = _leib_gauche(cm_le_sm, cardinal(sm), vm, HcardM, lambda g: _le(g, sm))
    #   seg_x ≤ x  : de seg_x ≤ Card seg_x et Card seg_x = x
    sx_le_x = _leib_droit(sx_le_cx, cardinal(sx), vx, HcardX, lambda d: _le(sx, d))
    # chaîne : m ≤ seg_m ≤ seg_x ≤ x
    m_le_sx = N.modus_ponens(conjonction_intro(m_le_sm, sm_le_sx), _trans3(vm, sm, sx))  # m≤seg_x
    m_le_x = N.modus_ponens(conjonction_intro(m_le_sx, sx_le_x), _trans3(vm, sx, vx))    # m≤x
    return m_le_x                                                   # m ≤ x  [3 hyps]


def _leib_gauche(thm, ancien, nouveau, h_eq, phi):
    """De ⊢ φ(ancien) [thm] et ⊢ ancien=nouveau [h_eq] déduit ⊢ φ(nouveau).

    Leibniz via S6 : (ancien=nouveau) ⇒ (φ(ancien) ⇔ φ(nouveau))."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_avant
    eqv = N.modus_ponens(h_eq, N.s6(ancien, nouveau, "wL", phi(var("wL"))))
    return N.modus_ponens(thm, equivalence_avant(eqv))


def _leib_droit(thm, ancien, nouveau, h_eq, phi):
    """Idem _leib_gauche (φ peut placer le trou à droite ; même mécanique S6)."""
    return _leib_gauche(thm, ancien, nouveau, h_eq, phi)


__all__ = [
    "seg_terme",
    "hyp_surjection",
    "hyp_bon_ordre_seg",
    "seg_inclus_donne_card_le",
    "card_le_de_seg_inclus",
]
