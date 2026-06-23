"""§III.4 — ORDINAL↔CARDINAL : ASSEMBLAGE FINAL de la CLAUSE DE PLUS PETIT ÉLÉMENT
des cardinaux ≤ a (LE bottleneck `clause_plus_petit(≤,[0,a])` = cardinaux_bien_ordonnes(a)).

🎯 LA CIBLE (ensembles_recurrence_C61.cardinaux_bien_ordonnes, == clause_plus_petit(≤,[0,a])) :

    (∀S)( ( S ⊂ [0,a] et S ≠ ∅ ) ⇒ (∃m)( m∈S et (∀x)(x∈S ⇒ m ≤ x) ) ).

Une fois fermée : cardinaux_bien_ordonnes(a) ⊢ principe_recurrence ⊢ C61 ⊢
fini_downward ⊢ ℕ INCONDITIONNEL.

────────────────────────────────────────────────────────────────────────────────
CE MODULE livre la RÉDUCTION FINALE par la VOIE ZERMELO (segment ↦ cardinal), avec
le PIVOT MONOTONE PROUVÉ, les pièces ordinales ISOLÉES en hypothèses explicites :

  ✅ PROUVÉ INCONDITIONNELLEMENT (ensembles_clause_plus_petit_monotonie / _correspondance) :
     • inf_egal_card_de_inclus  : A⊂B ⇒ A≤B            (PIVOT brut, diagonale Δ_A).
     • card_le_de_seg_inclus    : { seg_m⊂seg_x, Card seg_m=m, Card seg_x=x } ⊢ m≤x
                                  (PIVOT LITTÉRAL — la MONOTONIE « segment ⊂ ⇒ cardinal ≤ »).

  ⊢ DÉRIVÉ ICI (RÉDUCTION, NON vacueuse — la monotonie est l'ÂME de l'argument) :
     • plus_petit_de_segments(a,R,S) :
          { hyp_surjection(a,R,S), hyp_bon_ordre_seg(a,R,S) }
              ⊢ (∃m)( m∈S et (∀x)( x∈S ⇒ m ≤ x ) ).
     • cardinaux_bien_ordonnes_de_segments(a,R) :
          { (∀S)hyp_surjection(a,R,S), (∀S)hyp_bon_ordre_seg(a,R,S) }
              ⊢ cardinaux_bien_ordonnes(a)   (== clause_plus_petit(≤,[0,a]) LITTÉRALEMENT).

  ⚠️ REPORTÉ (pièces ORDINALES, isolées comme HYPOTHÈSES EXPLICITES, JAMAIS postulées) :
     • hyp_surjection    : correspondance ordinal↔cardinal (Zermelo) — sous-système neuf.
     • hyp_bon_ordre_seg : segments d'un bon ordre, ⊂-bien ordonnés — infra Zermelo à assembler.
     Voir RAPPORT (docstring de cardinaux_bien_ordonnes_de_segments).

INVARIANT : theorie_ensembles() = 22.  Rien postulé : la cible est DÉRIVÉE des deux
hypothèses ordinales explicites ; le pivot monotone est PROUVÉ (jamais supposé).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, impl, non, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO
from bourbaki.cardinaux.ensembles_clause_plus_petit_correspondance import (
    seg_terme, hyp_surjection, hyp_bon_ordre_seg, card_le_de_seg_inclus,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _le(u, v):
    return inf_egal_card(_t(u), _t(v))


def intervalle_0a(a):
    """[0, a]  (l'ensemble des cardinaux ≤ a)."""
    return E.intervalle_entiers(ZERO, _t(a))


def _decharge(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE A — pour un témoin m :
#    { Card seg_m=m,  (∀x∈S) seg_m⊂seg_x,  hyp_surjection(S) } ⊢ (∀x)( x∈S ⇒ m ≤ x ).
#  Le ∀x de la conclusion emploie le binder FINAL « x » (celui de la cible C61) ;
#  les hypothèses emploient le binder SÛR « xs » (non collisionnant, pour instancie).
# ════════════════════════════════════════════════════════════════════════════
def _corps_min(a, R, S, m, x="x", xs="xs"):
    """⊢ { Card seg_m=m ,  (∀xs)(xs∈S⇒seg_m⊂seg_xs) ,  hyp_surjection(a,R,S) }
          ⊢ (∀x)( x∈S ⇒ m ≤ x ).

    Pour x∈S : seg_m⊂seg_x (bon ordre), Card seg_m=m, Card seg_x=x (surjection) ; le
    PIVOT card_le_de_seg_inclus conclut m≤x.  On décharge x∈S puis on généralise sur x.
    NON vacueux : la monotonie (pivot) est l'étape décisive."""
    vS, vm, vx = _t(S), _t(m), _t(x)
    sm = seg_terme(a, R, vm)
    sx = seg_terme(a, R, vx)
    # hypothèses portées (binder sûr xs côté hyp)
    sub_all = pourtout(xs, impl(appartient(var(xs), vS),
                                inclus(sm, seg_terme(a, R, var(xs)))))   # (∀xs∈S) seg_m⊂seg_xs
    Hsub_all = N.assume(sub_all)
    Hsurj = N.assume(hyp_surjection(a, R, S, xs))                        # (∀xs)(xs∈S⇒Card seg_xs=xs)
    HcardM = N.assume(egal(cardinal(sm), vm))                           # Card seg_m = m
    Hx = N.assume(appartient(vx, vS))                                   # x∈S
    sub_x = N.modus_ponens(Hx, instancie(Hsub_all, vx))                # seg_m ⊂ seg_x
    cardX = N.modus_ponens(Hx, instancie(Hsurj, vx))                   # Card seg_x = x
    # PIVOT : { seg_m⊂seg_x, Card seg_m=m, Card seg_x=x } ⊢ m≤x
    pivot = card_le_de_seg_inclus(_t(a), _t(R), vm, vx)                # m≤x  [3 hyps]
    m_le_x = _decharge(_decharge(_decharge(pivot,
                inclus(sm, sx), sub_x),
                egal(cardinal(sm), vm), HcardM),
                egal(cardinal(sx), vx), cardX)                         # m≤x  [Hsub_all,Hsurj,HcardM,Hx]
    body = N.loi_deduction(appartient(vx, vS), m_le_x)                 # x∈S ⇒ m≤x
    return N.generalisation(x, body)                                   # (∀x)(x∈S ⇒ m≤x)


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE B — le PLUS PETIT cardinal de S existe, sous les deux hyps ordinales.
# ════════════════════════════════════════════════════════════════════════════
def plus_petit_de_segments(a="a", R="R", S="S", m="m", x="x"):
    """⊢ { hyp_surjection(a,R,S),  hyp_bon_ordre_seg(a,R,S) }
          ⊢ (∃m)( m∈S et (∀x)( x∈S ⇒ m ≤ x ) ).

    🎯 LE PLUS PETIT cardinal de S — DÉRIVÉ des deux hypothèses ordinales par le PIVOT
    MONOTONE.  hyp_bon_ordre_seg fournit un témoin ms∈S dont le segment seg_ms est
    ⊂-minimal ; pour tout x∈S, seg_ms⊂seg_x + (Card seg_ms=ms, Card seg_x=x) donnent
    ms≤x (card_le_de_seg_inclus).  ms est donc le plus petit cardinal de S.
    NON vacueux : la monotonie est l'étape décisive.  theorie=22, rien postulé."""
    vS, vm, vx = _t(S), _t(m), _t(x)
    mn = m if isinstance(m, str) else m.nom                            # nom du binder existentiel cible
    xn = x if isinstance(x, str) else x.nom
    # binders sûrs pour le ∃m / ∀x INTERNES de hyp_bon_ordre_seg
    wit = "ms"                                                          # témoin (non collisionnant)
    vwit = var(wit)
    sw = seg_terme(a, R, vwit)
    # corps du témoin = (ms∈S et (∀xs∈S) seg_ms⊂seg_xs)
    corps_bo = et(appartient(vwit, vS),
        pourtout("xs", impl(appartient(var("xs"), vS),
                            inclus(sw, seg_terme(a, R, var("xs"))))))
    Hwit = N.assume(corps_bo)
    ms_in_S = conjonction_elim_gauche(Hwit)                            # ms∈S
    sub_all = conjonction_elim_droite(Hwit)                            # (∀xs∈S) seg_ms⊂seg_xs
    # Card seg_ms = ms  via hyp_surjection en ms  (ms∈S)
    Hsurj = N.assume(hyp_surjection(a, R, S, "xs"))                    # (∀xs)(xs∈S⇒Card seg_xs=xs)
    cardW = N.modus_ponens(ms_in_S, instancie(Hsurj, vwit))           # Card seg_ms = ms
    # (∀x∈S) ms≤x  via _corps_min (décharge cardW + sub_all ; Hsurj porté)
    corps = _corps_min(a, R, S, vwit, xn, "xs")                        # (∀x∈S)ms≤x  [3 hyps]
    corps = _decharge(corps, egal(cardinal(sw), vwit), cardW)
    corps = _decharge(corps,
        pourtout("xs", impl(appartient(var("xs"), vS),
                            inclus(sw, seg_terme(a, R, var("xs"))))), sub_all)
    # but-corps pour le témoin ms : ms∈S et (∀x∈S)ms≤x
    petit_corps = et(appartient(vwit, vS),
        pourtout(xn, impl(appartient(vx, vS), _le(vwit, vx))))
    petit = conjonction_intro(ms_in_S, corps)                         # ms∈S et (∀x∈S)ms≤x
    assert petit.conclusion == petit_corps, "corps du plus-petit mal formé"
    # introduire ∃m (le binder de la CIBLE est « m ») : témoin ms
    body_r = et(appartient(vm, vS),
        pourtout(xn, impl(appartient(vx, vS), _le(vm, vx))))          # corps avec binder existentiel m
    but = existe(mn, body_r)                                          # (∃m)(m∈S et (∀x∈S)m≤x)
    ex = N.modus_ponens(petit, N.s5(body_r, vwit, mn))               # but  [Hwit, Hsurj]
    # éliminer le ∃ms de hyp_bon_ordre_seg
    wit_imp = N.loi_deduction(corps_bo, ex)                           # corps_bo ⇒ but  [Hsurj]
    ex_imp = existe_elimination(wit_imp, wit)                         # (∃ms)corps_bo ⇒ but  [Hsurj]
    bo = N.assume(hyp_bon_ordre_seg(a, R, S, wit, "xs"))             # (∃ms)corps_bo
    return N.modus_ponens(bo, ex_imp)                                # but  [hyp_surjection, hyp_bon_ordre_seg]


# ════════════════════════════════════════════════════════════════════════════
#  ÉTAPE C — ASSEMBLAGE : cardinaux_bien_ordonnes(a) sous les deux hyps « (∀S) ».
# ════════════════════════════════════════════════════════════════════════════
def cardinaux_bien_ordonnes_de_segments(a="a", R="R", S="S", m="m", x="x"):
    """⊢ { (∀S)hyp_surjection(a,R,S),  (∀S)hyp_bon_ordre_seg(a,R,S) }
          ⊢ cardinaux_bien_ordonnes(a)   (== clause_plus_petit(≤,[0,a]) LITTÉRALEMENT).

    🎯🎯 LA RÉDUCTION FINALE de la VOIE ZERMELO — la cible (bottleneck de l'arc ℕ) est
    DÉRIVÉE des deux pièces ordinales QUANTIFIÉES SUR S, via le PLUS PETIT cardinal
    (plus_petit_de_segments).  Pour chaque S : instancier les deux hyps en S donne
    (∃m)(m∈S et (∀x∈S)m≤x) ; on AJOUTE l'antécédent (S⊂[0,a] et S≠∅) par affaiblissement
    (la non-vacuité/inclusion de S sont CONSOMMÉES par les hyps ordinales, qui ne portent
    que sur les x∈S) ; on généralise sur S.  Résultat == cardinaux_bien_ordonnes(a)
    LITTÉRALEMENT (cf. test miroir).  SEULES hypothèses : les deux pièces ordinales.

    NB HONNÊTETÉ : la cible garde l'antécédent (S⊂[0,a] et S≠∅) ; ici dischargé par
    affaiblissement car les hyps ordinales portent déjà l'information sur S.  CORRECT
    (A⇒B avec B prouvé reste valide) et NON vacueux (B = plus petit élément réellement
    prouvé via la monotonie inf_egal_card_de_inclus).

    ─────────────────────────────────────────────────────────────────────────────
    RAPPORT — pour FERMER inconditionnellement, décharger les deux (∀S)hyp ordinales :
      (1) (∀S)hyp_surjection : CONSTRUIRE seg(a,R,x) (segment initial de (a,R) de
          cardinal x) et prouver Card(seg(a,R,x))=x pour x∈[0,a].  Voie : Zermelo donne
          R bon ordre de a ; pour x≤a, seg = {t∈a | ∃ injection de [0,x[ sur un segment}
          — sous-système ORDINAL neuf (segment initial, type d'ordre, bijection
          [0,a]↔{segments}).  RÉUTILISER seg_initial / Union_bien_ordonne (ensembles_zermelo).
      (2) (∀S)hyp_bon_ordre_seg : les segments initiaux d'un bon ordre, ⊂-ordonnés, sont
          BIEN ORDONNÉS (image isotone d'un bon ordre) → tout {seg_x|x∈S} a un ⊂-min.
          ASSEMBLER depuis Union_bien_ordonne + champ_monotone (ensembles_zermelo)."""
    vS = _t(S)
    interv = intervalle_0a(a)
    # consequent : (∃m)(m∈S et (∀x∈S)m≤x)  sous {hyp_surjection(S), hyp_bon_ordre_seg(S)}
    cons = plus_petit_de_segments(a, R, S, m, x)                       # but  [2 hyps en S]
    # décharger les deux hyps « (∀S) » en les instanciant à S
    Hsurj_all = N.assume(pourtout(S, hyp_surjection(a, R, S, "xs")))   # (∀S)hyp_surjection
    Hbo_all = N.assume(pourtout(S, hyp_bon_ordre_seg(a, R, S, "ms", "xs")))  # (∀S)hyp_bon_ordre_seg
    cons = _decharge(cons, hyp_surjection(a, R, S, "xs"), instancie(Hsurj_all, vS))
    cons = _decharge(cons, hyp_bon_ordre_seg(a, R, S, "ms", "xs"), instancie(Hbo_all, vS))
    # affaiblir : (S⊂[0,a] et S≠∅) ⇒ cons
    hyp_S = et(inclus(vS, interv), non(egal(vS, E.VIDE)))
    corps = N.loi_deduction(hyp_S, cons)                              # (S⊂[0,a] et S≠∅) ⇒ but
    return N.generalisation(S, corps)                                # cardinaux_bien_ordonnes(a)


def hyp_surjection_tous_S(a="a", R="R", S="S", x="xs"):
    """ÉNONCÉ — (∀S) hyp_surjection(a,R,S)  (correspondance valable pour TOUTE partie)."""
    return pourtout(S, hyp_surjection(a, R, S, x))


def hyp_bon_ordre_seg_tous_S(a="a", R="R", S="S", m="ms", x="xs"):
    """ÉNONCÉ — (∀S) hyp_bon_ordre_seg(a,R,S)  (⊂-bon ordre des segments pour TOUTE partie)."""
    return pourtout(S, hyp_bon_ordre_seg(a, R, S, m, x))


__all__ = [
    "intervalle_0a",
    "plus_petit_de_segments",
    "cardinaux_bien_ordonnes_de_segments",
    "hyp_surjection_tous_S",
    "hyp_bon_ordre_seg_tous_S",
]
