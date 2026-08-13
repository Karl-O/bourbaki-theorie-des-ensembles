"""§III.4 — CORRESPONDANCE ORDINAL↔CARDINAL : réduction de cardinaux_bien_ordonnes(a)
au BON ORDRE de l'intervalle [0,a] par l'ordre (induit) des cardinaux.

────────────────────────────────────────────────────────────────────────────────
CIBLE (ensembles_recurrence_C61.cardinaux_bien_ordonnes) :

    cardinaux_bien_ordonnes(a) =
        (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) ).

DÉCOUVERTE STRUCTURELLE (vérifiée par égalité de formules) :

    cardinaux_bien_ordonnes(a)  ==  clause_plus_petit( ≤ , [0,a] )

où clause_plus_petit(R,E) est EXACTEMENT le 2ᵉ conjoint de est_bien_ordonne(R,E)
(la clause « toute partie non vide a un plus petit élément », Déf. 1 E.III.2.1) et
≤ est l'ordre BARE des cardinaux (inf_egal_card).  Voir le test miroir.

CONSÉQUENCE — la cible se RÉDUIT à un bon ordre :

    est_bien_ordonne( ≤_induit , [0,a] )  ⊢  cardinaux_bien_ordonnes(a)

par l'ENGINE bon_ordre → clause (ensembles_ordinal_cardinal_bon_ordre), modulo
le passage de l'ordre INDUIT (qui satisfait la réflexivité-dans-E de la Déf. 1 :
x≤x ⇔ x∈[0,a]) à l'ordre BARE de la clause-cible (sur S⊂[0,a], les deux coïncident,
car m,x∈[0,a]).  Cette réduction induit↔bare est PROUVÉE INCONDITIONNELLEMENT ici.

────────────────────────────────────────────────────────────────────────────────
RÉPARTITION DU SALVAGE (graduée, honnête) :

  ✅ INCONDITIONNEL (ce module) :
     • ordre_induit_intervalle      — l'ordre ≤ induit sur [0,a].
     • clause_induite_donne_bare    — sur [0,a], la clause induite ⇒ la clause bare
                                       (cible) : un plus petit pour ≤_induit est un
                                       plus petit pour ≤.  [cœur du passage induit→bare]
     • cardinaux_bien_ordonnes_de_bon_ordre :
            { est_bien_ordonne(≤_induit, [0,a]) } ⊢ cardinaux_bien_ordonnes(a).
       LA RÉDUCTION COMPLÈTE — l'unique hypothèse restante est le BON ORDRE de [0,a].

  ⚠️ REPORTÉ (le BOTTLENECK ordinal↔cardinal, isolé comme HYPOTHÈSE explicite) :
     • bon_ordre_intervalle_via_zermelo :
            est_bien_ordonne(≤_induit, [0,a])  — l'intervalle des cardinaux ≤ a est
       bien ordonné par ≤.  Voie : ZERMELO (bon ordre R du SET a) → chaque cardinal
       x≤a = Card d'un segment initial de (a,R) → l'ordre des cardinaux ≤a est le
       type d'ordre des segments, donc bien ordonné.  Cette CORRESPONDANCE
       ordinal↔cardinal (segment initial ↦ son cardinal) n'est PAS encore construite
       dans le projet (théorie ordinale représentationnelle) → posée en HYPOTHÈSE,
       JAMAIS postulée comme théorème.  Voir le rapport pour le découpage précis.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la cible est DÉRIVÉE d'une
hypothèse explicite (le bon ordre), elle-même le seul report.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import monotonie_existe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ordinal_cardinal.ordinal_cardinal_correspondance.ensembles_ordinal_cardinal_bon_ordre import (
    clause_plus_petit, plus_petit_de_bon_ordre,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _le(u, v):
    """L'ordre BARE des cardinaux  u ≤ v  (inf_egal_card)."""
    return inf_egal_card(_t(u), _t(v))


def intervalle_0a(a):
    """[0, a] = intervalle_entiers(0, a)  (E.III.5.3) — l'ensemble des cardinaux ≤ a."""
    return E.intervalle_entiers(ZERO, _t(a))


def ordre_induit_intervalle(a):
    """L'ordre des cardinaux ≤ INDUIT sur [0,a] :  R{u,v} := ( u≤v et u∈[0,a] et v∈[0,a] ).

    C'est ordre_induit(≤, [0,a]) (E.III.1.1, Exemple 2).  Contrairement à l'ordre
    BARE ≤, cet ordre induit vérifie la réflexivité-DANS-E de la Définition 1
    (x≤x ⇔ x∈[0,a]) : c'est donc LUI qui peut bien ordonner [0,a] au sens de
    est_bien_ordonne (E.III.2.1).  La clause de plus petit élément de CE bon ordre
    se ramène (sur S⊂[0,a]) à la clause BARE de la cible (clause_induite_donne_bare)."""
    interv = intervalle_0a(a)
    return lambda u, v: et(et(_le(u, v), appartient(_t(u), interv)),
                           appartient(_t(v), interv))


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR DU PASSAGE INDUIT → BARE  : sur S ⊂ [0,a], la clause de plus petit pour
#  l'ordre INDUIT entraîne la clause de plus petit pour l'ordre BARE (la cible).
#
#  Un plus petit m pour ≤_induit : m∈S et (∀x)(x∈S ⇒ (m≤x et m∈[0,a] et x∈[0,a])).
#  En projetant le 1er conjoint (m≤x), on obtient m∈S et (∀x)(x∈S ⇒ m≤x), c.-à-d. le
#  plus petit pour ≤ BARE.  (On n'a même pas besoin de S⊂[0,a] pour CETTE projection.)
# ════════════════════════════════════════════════════════════════════════════
def plus_petit_induit_donne_bare(a, S="S", m="m", x="x"):
    """⊢ ( m∈S et (∀x)(x∈S ⇒ R_induit{m,x}) ) ⇒ ( m∈S et (∀x)(x∈S ⇒ m≤x) ).

    Projette le 1er conjoint (m≤x) de R_induit{m,x} = (m≤x et m∈[0,a] et x∈[0,a]).
    INCONDITIONNEL — pure logique propositionnelle + généralisation."""
    vS, vm, vx = _t(S), _t(m), _t(x)
    Rind = ordre_induit_intervalle(a)
    corps_induit = pourtout(x, impl(appartient(vx, vS), Rind(vm, vx)))
    hyp = et(appartient(vm, vS), corps_induit)
    H = N.assume(hyp)
    m_in_S = conjonction_elim_gauche(H)                    # m∈S
    body_ind = conjonction_elim_droite(H)                  # (∀x)(x∈S ⇒ R_induit{m,x})
    # per-x : (x∈S ⇒ R_induit{m,x}) ⊢ (x∈S ⇒ m≤x)
    inst = instancie(body_ind, vx)                         # x∈S ⇒ R_induit{m,x}
    hx = N.assume(appartient(vx, vS))                      # x∈S
    rind = N.modus_ponens(hx, inst)                        # R_induit{m,x} = (m≤x et m∈[0,a]) et x∈[0,a]
    mlex = conjonction_elim_gauche(conjonction_elim_gauche(rind))   # m≤x
    body_bare_x = N.loi_deduction(appartient(vx, vS), mlex)         # x∈S ⇒ m≤x
    body_bare = N.generalisation(x, body_bare_x)           # (∀x)(x∈S ⇒ m≤x)
    concl = conjonction_intro(m_in_S, body_bare)           # m∈S et (∀x)(x∈S ⇒ m≤x)
    return N.loi_deduction(hyp, concl)


def clause_induite_donne_bare(a, S="S", m="m", x="x"):
    """⊢ (∃m)( m∈S et (∀x)(x∈S ⇒ R_induit{m,x}) )
            ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m≤x) ).

    Monotonie du ∃m appliquée à plus_petit_induit_donne_bare.  Le plus petit élément
    de S pour l'ordre INDUIT est aussi le plus petit pour l'ordre BARE des cardinaux.
    INCONDITIONNEL."""
    vm = _t(m)
    Rind = ordre_induit_intervalle(a)
    vS, vx = _t(S), _t(x)
    P_ind = et(appartient(vm, vS), pourtout(x, impl(appartient(vx, vS), Rind(vm, vx))))
    P_bare = et(appartient(vm, vS), pourtout(x, impl(appartient(vx, vS), _le(vm, vx))))
    step = plus_petit_induit_donne_bare(a, S, m, x)        # P_ind ⇒ P_bare
    assert step.conclusion == impl(P_ind, P_bare)
    return monotonie_existe(step, m)                       # (∃m)P_ind ⇒ (∃m)P_bare


# ════════════════════════════════════════════════════════════════════════════
#  RÉDUCTION COMPLÈTE :  bon ordre de [0,a]  ⊢  cardinaux_bien_ordonnes(a)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §3.2 Demo.1 | E III.24 L.16-30 | PDF p.127
def cardinaux_bien_ordonnes_de_bon_ordre(a="a", S="S", m="m", x="x",
                                         xo="xo", yo="yo", zo="zo"):
    """⊢ { est_bien_ordonne( ≤_induit , [0,a] ) }  ⊢  cardinaux_bien_ordonnes(a).

    🎯 LA RÉDUCTION — la cible cardinaux_bien_ordonnes(a) est DÉRIVÉE de l'UNIQUE
    hypothèse « [0,a] est bien ordonné par l'ordre (induit) des cardinaux ».

    Pour chaque partie S de [0,a] non vide :
      • l'ENGINE plus_petit_de_bon_ordre (INCONDITIONNEL) extrait, du bon ordre,
        (∃m)( m∈S et (∀x)(x∈S ⇒ R_induit{m,x} ) ) ;
      • clause_induite_donne_bare projette R_induit{m,x} sur m≤x (INCONDITIONNEL),
        donnant (∃m)( m∈S et (∀x)(x∈S ⇒ m≤x ) ) ;
      • on décharge S⊂[0,a] et S≠∅, on généralise sur S.

    Le résultat == cardinaux_bien_ordonnes(a) LITTÉRALEMENT (cf. test miroir).
    SEULE hypothèse restante : le BON ORDRE de [0,a] (report ordinal↔cardinal).
    theorie=22, rien postulé."""
    va, vS = _t(a), _t(S)
    interv = intervalle_0a(a)
    Rind = ordre_induit_intervalle(a)
    # ENGINE : { est_bien_ordonne(R_induit,[0,a]), S⊂[0,a], S≠∅ } ⊢ (∃m)(m∈S et ...induit)
    pp_induit = plus_petit_de_bon_ordre(Rind, interv, S, xo, yo, zo, m, x)
    # projeter induit → bare
    bare_imp = clause_induite_donne_bare(a, S, m, x)       # (∃m)…induit ⇒ (∃m)…bare
    pp_bare = N.modus_ponens(pp_induit, bare_imp)          # (∃m)(m∈S et (∀x)(x∈S ⇒ m≤x))
    # reconstruire ( (S⊂[0,a] et S≠∅) ⇒ (∃m)… ) en remplaçant les 2 hyps de partie
    # par la conjonction hyp_S décomposée.
    hyp_S = et(inclus(vS, interv), non(egal(vS, E.VIDE)))
    Hs = N.assume(hyp_S)
    # pp_bare a pour hyps {bon ordre, S⊂[0,a], S≠∅} ; on remplace les 2 dernières
    # par la conjonction hyp_S décomposée.
    sub = conjonction_elim_gauche(Hs)                      # S⊂[0,a]
    ne = conjonction_elim_droite(Hs)                       # S≠∅
    pp1 = _decharge(pp_bare, inclus(vS, interv), sub)
    pp2 = _decharge(pp1, non(egal(vS, E.VIDE)), ne)        # (∃m)…  [hyps: bon ordre, hyp_S]
    corps = N.loi_deduction(hyp_S, pp2)                    # (S⊂[0,a] et S≠∅) ⇒ (∃m)…
    return N.generalisation(S, corps)                     # (∀S)(...) = cardinaux_bien_ordonnes(a)


def _decharge(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  REPORT ISOLÉ — le BON ORDRE de [0,a] (bottleneck ordinal↔cardinal), ÉNONCÉ
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_intervalle(a="a", x="xo", y="yo", z="zo", X="S", b="m", w="x"):
    """ÉNONCÉ « [0,a] est bien ordonné par l'ordre (induit) des cardinaux » :

        est_bien_ordonne( ≤_induit , [0,a] ).

    ⚠️ NON PROUVÉ (REPORTÉ — bottleneck ordinal↔cardinal).  C'est, AVEC SES BINDERS PAR
    DÉFAUT, LITTÉRALEMENT l'UNIQUE hypothèse résiduelle de
    cardinaux_bien_ordonnes_de_bon_ordre (vérifié par égalité de formules dans le test
    miroir).  Voie (Zermelo) : un bon ordre R du SET a (zermelo()) ; chaque cardinal
    ≤a = Card d'un segment initial de (a,R) ; l'ordre des cardinaux ≤a est alors le
    type d'ordre des segments initiaux, bien ordonné.  La CORRESPONDANCE
    segment_initial ↦ son cardinal (et la monotonie du cardinal des segments) n'existe
    pas encore dans le projet → reportée ICI comme formule-énoncé."""
    Rind = ordre_induit_intervalle(a)
    return E.est_bien_ordonne(Rind, intervalle_0a(a), x, y, z, X, b, w)


__all__ = [
    "intervalle_0a", "ordre_induit_intervalle",
    "plus_petit_induit_donne_bare", "clause_induite_donne_bare",
    "cardinaux_bien_ordonnes_de_bon_ordre",
    "bon_ordre_intervalle",
]
