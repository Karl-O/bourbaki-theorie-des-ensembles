"""§III.4 — PREUVE de `hyp_transport_ordinal` : DÉCHARGE des conjoints du PULLBACK.

────────────────────────────────────────────────────────────────────────────────
OBJECTIF.  `bon_ordre_intervalle_ordinal(a)` (ensembles_bon_ordre_intervalle_ordinal,
le GATE ℕ) prouve `bon_ordre_intervalle(a)` sous l'UNIQUE hypothèse résiduelle

    hyp_transport_ordinal(a)  =
        (∃Ro)( est_bien_ordonne(Ro,a)
               et (∀S)( ( S⊂[0,a] et S≠∅ ) ⇒
                        ( PB⊂a  et  PB≠∅  et  INTO  et  ONTO ) ) )        avec
        PB   = pullback(a,Ro,S) = { t∈a | Card(seg(a,Ro,t)) ∈ S }   (terme opaque),
        INTO = hyp_realisation_min(Ro,a,S,PB) = (∀t)( t∈PB ⇒ Card(seg(a,Ro,t)) ∈ S ),
        ONTO = hyp_realisation_onto(Ro,a,S,PB) =
               (∀c)( c∈S ⇒ (∃t)( t∈PB et c = Card(seg(a,Ro,t)) ) ).

Ce module CONSTRUIT le pullback comme un VRAI ensemble (sélection S8 dans a) et
DÉCHARGE — INCONDITIONNELLEMENT — les conjoints qui en découlent directement, en
réduisant le tout à UN SEUL maillon mathématique HONNÊTE (la RÉALISATION : tout
cardinal ≤a est le cardinal d'un segment initial de (a,Ro)).  theorie_ensembles()=22.

────────────────────────────────────────────────────────────────────────────────
LE PULLBACK COMME ENSEMBLE (sélection S8, motif axiome_W / diagonale_cantor /
axiome_exposant).  Le terme opaque `pullback(a,Ro,S)` reçoit ICI son AXIOME
DÉFINITIONNEL de membre (sélection S8 dans a, unicité A1) — DANS UNE THÉORIE
DÉDIÉE, donc theorie_ensembles() reste 22, RIEN n'est postulé :

    (∀t)( t ∈ pullback(a,Ro,S)  ⇔  ( t∈a  et  Card(seg(a,Ro,t)) ∈ S ) ).

C'est EXACTEMENT la collectivisation S8 du prédicat « t∈a et Card(seg(a,Ro,t))∈S »
en t (relation de t, paramètres a,Ro,S).  De cette équivalence :

  ✅ pullback_into        : (∀t)( t∈PB ⇒ Card(seg(a,Ro,t)) ∈ S )   [= INTO, CLOS].
  ✅ pullback_inclus_a    : PB ⊂ a                                  [CLOS].

────────────────────────────────────────────────────────────────────────────────
LE SEUL MAILLON HONNÊTE — la RÉALISATION (ordinal↔cardinal, surjectivité) :

    realisation_segment(Ro,a,c)  =  ( c ≤ a )  ⇒  (∃t)( t∈a  et  Card(seg(a,Ro,t)) = c ).

« Tout cardinal c≤a est le cardinal d'un segment initial seg(a,Ro,t) de (a,Ro) »
(c≤a := (∃F) F injecte c dans a ; E.III.3.2).  C'est le théorème de représentation
ordinal (≈ effondrement de Mostowski) : B:=image(F)⊂a, bien ordonné par Ro|B, est
order-iso à un segment initial seg(a,Ro,t) (sous-bon-ordre iso à segment initial),
donc Card(seg(a,Ro,t))=Card(B)=c.  Cette représentation n'est PAS encore close dans
le projet (cf. RAPPORT) ; ISOLÉE ICI en hypothèse, JAMAIS postulée.  De ce maillon :

  ⊢ (sous realisation_segment + S⊂[0,a])   pullback_onto  : ONTO.
  ⊢ (sous realisation_segment + S⊂[0,a] + S≠∅)             pullback_non_vide : PB≠∅.

────────────────────────────────────────────────────────────────────────────────
⚠️ BLOCAGE STRUCTUREL pour le `==` EXACT avec hyp_transport_ordinal(a)  (RAPPORTÉ).

Le conjoint est_bien_ordonne(Ro,a) tel que hyp_transport_ordinal le DÉPOSE (via
`_bo_form_canon`, qui passe le TERME `pullback(a,Ro,S)` dans le slot du LIANT « X »
de est_bien_ordonne) est une formule où un TERME COMPOSÉ occupe une position de
LIANT ∀ : `∀(pullback_seg_card(a,Ro,S)) ( … )`.  AUCUNE règle du noyau ne peut
PRODUIRE un liant-terme : generalisation(x:str,·), s5/existe, alpha_existe(x,y,·)
ne lient QUE des NOMS DE VARIABLE (alpha_existe substitue var(y)).  Ce conjoint
n'est donc DÉRIVABLE par aucun moyen honnête — il ne peut qu'être ASSUMÉ (comme le
fait bon_ordre_intervalle_ordinal lui-même).  La cible exacte hyp_transport_ordinal(a)
est par conséquent NON close tant que ce liant-terme reste dans sa définition.

Ce module livre donc le MAXIMUM honnête : la machinerie S8 du pullback, INTO et ⊂a
CLOS, ONTO et ≠∅ réduits au SEUL maillon RÉALISATION ; et `hyp_transport_corps_preuve`
qui assemble le CORPS du ∀S — `( PB⊂a et PB≠∅ et INTO et ONTO )` — sous les hypothèses
HONNÊTES { bo(Ro,a), realisation_segment(Ro,a,·) } (Ro bien formé, PAS le liant-terme).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus, equiv,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.cardinaux.ensembles_segments_construction import seg, _R_de
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, inf_egal_card
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import intervalle_0a
import bourbaki.cardinaux.ensembles_bon_ordre_intervalle_ordinal as BOIO


def _t(t):
    return t if isinstance(t, Terme) else var(t)


_HOLE = "hole_htop"


def _decharge(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _sym(a, b, h_ab):
    """De ⊢ a=b [h_ab] déduit ⊢ b=a  (S6, trou FRAIS)."""
    eqv = N.modus_ponens(h_ab, N.s6(_t(a), _t(b), _HOLE, egal(var(_HOLE), _t(a))))
    return N.modus_ponens(N.reflexivite(_t(a)), equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  Le PULLBACK comme ENSEMBLE : axiome DÉFINITIONNEL de membre (sélection S8).
#  Réutilise le TERME opaque `pullback(a,Ro,S)` de ensembles_bon_ordre_intervalle_
#  ordinal (pullback_seg_card).  Axiome posé en THÉORIE DÉDIÉE ⇒ theorie=22 intacte.
# ════════════════════════════════════════════════════════════════════════════
def pullback(a, Ro, S):
    """pullback(a,Ro,S) := { t∈a | Card(seg(a,Ro,t)) ∈ S }  (le MÊME terme opaque que
    ensembles_bon_ordre_intervalle_ordinal.pullback — pullback_seg_card)."""
    return BOIO.pullback(a, Ro, S)


def _corps_membre(a, Ro, S, t):
    """Le corps de la sélection :  ( t∈a  et  Card(seg(a,Ro,t)) ∈ S )."""
    return et(appartient(_t(t), _t(a)),
              appartient(cardinal(seg(Ro, a, _t(t))), _t(S)))


def axiome_pullback(a="a", Ro="Ro", S="S", t="t"):
    """⊢-schéma (∀t)( t ∈ pullback(a,Ro,S) ⇔ ( t∈a et Card(seg(a,Ro,t)) ∈ S ) ).

    Axiome DÉFINITIONNEL du pullback (sélection S8 du prédicat « t∈a et
    Card(seg(a,Ro,t))∈S » en t, unicité A1 ; motif axiome_W / diagonale_cantor /
    axiome_exposant).  Paramètres a,Ro,S ; instancié via theorie_pullback.
    N'ALTÈRE PAS theorie_ensembles()."""
    tn = t if isinstance(t, str) else t.nom
    vt = var(tn)
    return pourtout(tn, equiv(appartient(vt, pullback(a, Ro, S)),
                              _corps_membre(a, Ro, S, vt)))


def theorie_pullback(a="a", Ro="Ro", S="S", t="t"):
    """Théorie DÉDIÉE ne contenant que l'axiome de sélection du pullback (E.III.4)."""
    return N.Theorie("Pullback-seg-card", [axiome_pullback(a, Ro, S, t)])


def pullback_membre(a="a", Ro="Ro", S="S", t="t"):
    """⊢ ( t ∈ pullback(a,Ro,S) )  ⇔  ( t∈a  et  Card(seg(a,Ro,t)) ∈ S ).

    L'axiome de sélection instancié au TERME var(t)."""
    ax = N.axiome(theorie_pullback(a, Ro, S, t), axiome_pullback(a, Ro, S, t))
    return instancie(ax, _t(t))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ INTO  (pullback_into) : (∀t)( t∈PB ⇒ Card(seg(a,Ro,t)) ∈ S )   — CLOS.
#     == hyp_realisation_min(Ro,a,S,PB) (la forme du conjoint INTO de la cible).
# ════════════════════════════════════════════════════════════════════════════
def pullback_into(a="a", Ro="Ro", S="S", t="tt"):
    """⊢ (∀t)( t ∈ pullback(a,Ro,S)  ⇒  Card(seg(a,Ro,t)) ∈ S ).

    🎯 LE CONJOINT « INTO » du pullback, CLOS et INCONDITIONNEL.  De la sélection
    (pullback_membre), t∈PB ⇒ ( t∈a et Card(seg t)∈S ) ⇒ Card(seg t)∈S.  Conclusion
    == hyp_realisation_min(Ro,a,S,PB) (test miroir).  theorie=22, NON vacueux."""
    tn = t if isinstance(t, str) else t.nom
    vt = var(tn)
    PB = pullback(a, Ro, S)
    Ht = N.assume(appartient(vt, PB))                          # t∈PB
    corps = N.modus_ponens(Ht, equivalence_avant(pullback_membre(a, Ro, S, tn)))
    card_in_S = conjonction_elim_droite(corps)                 # Card(seg(a,Ro,t)) ∈ S
    body = N.loi_deduction(appartient(vt, PB), card_in_S)      # t∈PB ⇒ Card(seg t)∈S
    res = N.generalisation(tn, body)
    assert res.conclusion == BOIO.hyp_realisation_min(Ro, a, S, PB, tn), \
        "INTO ≠ hyp_realisation_min canonique"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ✅ PB ⊂ a  (pullback_inclus_a) — CLOS.
# ════════════════════════════════════════════════════════════════════════════
def pullback_inclus_a(a="a", Ro="Ro", S="S", t="z"):
    """⊢ pullback(a,Ro,S) ⊂ a.

    🎯 Le conjoint « PB⊂a » CLOS.  De la sélection, t∈PB ⇒ ( t∈a et … ) ⇒ t∈a ;
    binder canonique « z » de l'inclusion.  theorie=22, NON vacueux."""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import _peler_pourtout
    va = _t(a)
    PB = pullback(a, Ro, S)
    cible = inclus(PB, va)
    bndr, _ = _peler_pourtout(cible)                           # binder canonique de ⊂
    vz = var(bndr)
    Hz = N.assume(appartient(vz, PB))                          # z∈PB
    corps = N.modus_ponens(Hz, equivalence_avant(pullback_membre(a, Ro, S, bndr)))
    z_in_a = conjonction_elim_gauche(corps)                    # z∈a
    body = N.loi_deduction(appartient(vz, PB), z_in_a)
    res = N.generalisation(bndr, body)
    assert res.conclusion == inclus(PB, va), "PB⊂a mal formé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  LE MAILLON HONNÊTE — la RÉALISATION (ordinal↔cardinal).
# ════════════════════════════════════════════════════════════════════════════
def realisation_segment(Ro="Ro", a="a", c="cc", t="xs"):
    """ÉNONCÉ (maillon honnête) — « tout cardinal c≤a est le cardinal d'un segment
    initial de (a,Ro) » :

        ( c ≤ a )  ⇒  (∃t)( t∈a  et  Card(seg(a,Ro,t)) = c ).

    ⚠️ NON PROUVÉ — la RÉALISATION / surjectivité cardinal↦segment-initial.  c≤a
    fournit une injection F:c→a (inf_egal_card) ; B:=image(F)⊂a, bien ordonné par
    Ro|B, est order-iso à un segment initial seg(a,Ro,t) de (a,Ro) (sous-bon-ordre
    ≅ segment initial), d'où Card(seg(a,Ro,t))=Card(B)=c.  Théorème de représentation
    ordinal, NON encore clos (cf. RAPPORT).  Isolé en HYPOTHÈSE, JAMAIS postulé."""
    cn = c if isinstance(c, str) else c.nom
    tn = t if isinstance(t, str) else t.nom
    vc, vt = var(cn), var(tn)
    return impl(inf_egal_card(vc, _t(a)),
                existe(tn, et(appartient(vt, _t(a)),
                              egal(cardinal(seg(Ro, a, vt)), vc))))


# ════════════════════════════════════════════════════════════════════════════
#  ✅ (sous realisation_segment + S⊂[0,a])  ONTO  (pullback_onto).
#     ONTO = (∀c)( c∈S ⇒ (∃t)( t∈PB et c = Card(seg(a,Ro,t)) ) ).
# ════════════════════════════════════════════════════════════════════════════
def _inclus_S_interv(a, S, t):
    """⊢ ( t ∈ S ) ⇒ ( t ∈ [0,a] )  sous l'hypothèse S⊂[0,a]  (instanciée au TERME t)."""
    Hsub = N.assume(inclus(_t(S), intervalle_0a(a)))
    return instancie(Hsub, _t(t))


def _c_le_a(a, c, h_c_interv):
    """De ⊢ c∈[0,a] [h_c_interv] déduit ⊢ c ≤ a  (intervalle_implique_borne_sup, [0,a])."""
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import intervalle_implique_borne_sup
    from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import ZERO
    # intervalle_implique_borne_sup(0,a,c) : c∈[0,a] ⇒ c ≤ a, généralisé puis instancié.
    gen = N.generalisation("Xb", N.generalisation("Yb", N.generalisation("xb",
        intervalle_implique_borne_sup("Xb", "Yb", "xb"))))
    imp = instancie(instancie(instancie(gen, ZERO), _t(a)), _t(c))
    return N.modus_ponens(h_c_interv, imp)                      # c ≤ a


def pullback_onto(a="a", Ro="Ro", S="S", c="x", t="xw", w="xs"):
    """⊢ { S⊂[0,a],  (∀c) realisation_segment(Ro,a,c) }
            ⊢ (∀c)( c∈S ⇒ (∃t)( t∈pullback(a,Ro,S)  et  c = Card(seg(a,Ro,t)) ) ).

    🎯 LE CONJOINT « ONTO » réduit au maillon RÉALISATION.  Pour c∈S⊂[0,a] : c≤a
    (intervalle_implique_borne_sup) ; realisation_segment donne t∈a avec Card(seg t)=c,
    donc Card(seg t)∈S (=c∈S, Leibniz) ⇒ t∈PB (sélection) ; et c=Card(seg t) (sym).
    Conclusion == hyp_realisation_onto(Ro,a,S,PB) (test miroir).  theorie=22, NON vacueux."""
    cn = c if isinstance(c, str) else c.nom
    tn = t if isinstance(t, str) else t.nom
    wn = w if isinstance(w, str) else w.nom
    vc, vt = var(cn), var(tn)
    va, vS = _t(a), _t(S)
    PB = pullback(a, Ro, S)

    # (∀c) realisation_segment(Ro,a,c)  →  instance à c  [binder interne tn]
    H_real = N.assume(pourtout(cn, realisation_segment(Ro, a, cn, tn)))
    Hc = N.assume(appartient(vc, vS))                          # c∈S
    c_interv = N.modus_ponens(Hc, _inclus_S_interv(a, S, vc))  # c∈[0,a]
    c_le_a = _c_le_a(a, vc, c_interv)                          # c ≤ a
    real_c = instancie(H_real, vc)                             # c≤a ⇒ (∃t)(t∈a et Card(seg t)=c)
    ex_t = N.modus_ponens(c_le_a, real_c)                      # (∃t)( t∈a et Card(seg t)=c )

    # per-témoin t : ( t∈a et Card(seg t)=c ) ⊢ ( t∈PB et c=Card(seg t) )
    cardseg = cardinal(seg(Ro, a, vt))
    corps_t = et(appartient(vt, va), egal(cardseg, vc))
    Ht = N.assume(corps_t)
    t_in_a = conjonction_elim_gauche(Ht)                       # t∈a
    eq_cardseg_c = conjonction_elim_droite(Ht)                 # Card(seg t) = c
    # Card(seg t) ∈ S  (de c∈S et Card(seg t)=c, Leibniz : remplacer c par Card(seg t))
    c_eq_cardseg = _sym(cardseg, vc, eq_cardseg_c)             # c = Card(seg t)
    # Card(seg t)∈S : Leibniz transport de c∈S le long de c=Card(seg t)
    cardseg_in_S = _leib_transport(vc, cardseg, c_eq_cardseg,
                                   lambda w: appartient(w, vS), Hc)  # Card(seg t)∈S
    # t∈PB  (sélection arrière : t∈a et Card(seg t)∈S)
    corps_membre = conjonction_intro(t_in_a, cardseg_in_S)
    t_in_PB = N.modus_ponens(corps_membre, equivalence_arriere(pullback_membre(a, Ro, S, tn)))
    # ( t∈PB et c=Card(seg t) )
    cible_corps = conjonction_intro(t_in_PB, c_eq_cardseg)
    assert cible_corps.conclusion == et(appartient(vt, PB), egal(vc, cardseg)), \
        "corps ONTO mal formé"
    # introduire (∃t) [binder « xw » = celui de hyp_realisation_onto]
    body_ex = et(appartient(vt, PB), egal(vc, cardseg))
    ex_intro = N.modus_ponens(cible_corps, N.s5(body_ex, vt, tn))   # (∃t)( t∈PB et c=Card(seg t) )
    wit_imp = N.loi_deduction(corps_t, ex_intro)
    ex_from = N.modus_ponens(ex_t, existe_elimination(wit_imp, tn))  # (∃t)(t∈PB et c=Card seg t)
    body_c = N.loi_deduction(appartient(vc, vS), ex_from)       # c∈S ⇒ (∃t)…
    res = N.generalisation(cn, body_c)
    assert res.conclusion == BOIO.hyp_realisation_onto(Ro, a, S, PB, cn, tn), \
        "ONTO ≠ hyp_realisation_onto canonique"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ✅ (sous realisation_segment + S⊂[0,a] + S≠∅)  PB≠∅  (pullback_non_vide).
# ════════════════════════════════════════════════════════════════════════════
def pullback_non_vide(a="a", Ro="Ro", S="S", c=BOIO._BC, t=BOIO._BX):
    """⊢ { S⊂[0,a],  S≠∅,  (∀c) realisation_segment(Ro,a,c) }
            ⊢ ¬( pullback(a,Ro,S) = ∅ ).

    🎯 Le conjoint « PB≠∅ » réduit au maillon RÉALISATION.  S≠∅ fournit c∈S
    (non_vide_ssi_element) ; ONTO réalise c par un t∈PB, donc PB=∅ donnerait t∈∅
    (ex falso) — contradiction, donc PB≠∅.  theorie=22, NON vacueux."""
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide import non_vide_ssi_element
    cn = c if isinstance(c, str) else c.nom
    tn = t if isinstance(t, str) else t.nom
    vc, vt = var(cn), var(tn)
    va, vS = _t(a), _t(S)
    PB = pullback(a, Ro, S)

    # S≠∅ ⇒ (∃z) z∈S   (non_vide_ssi_element, binder « z ») → α-renomme « z »→cn
    nv = non_vide_ssi_element(vS)                              # ¬(S=∅) ⇔ (∃z) z∈S
    H_ne = N.assume(non(egal(vS, E.VIDE)))                     # S≠∅
    ex_z = N.modus_ponens(H_ne, equivalence_avant(nv))        # (∃z) z∈S
    from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_existe
    ex_c = N.modus_ponens(ex_z, equivalence_avant(
        alpha_existe("z", cn, appartient(var("z"), vS))))      # (∃c) c∈S

    # ONTO (réduit) : c∈S ⇒ (∃t)( t∈PB et c=Card(seg t) )
    onto = pullback_onto(a, Ro, S, cn, tn)                     # [S⊂[0,a], real] ⊢ (∀c)(c∈S ⇒ …)
    onto_c = instancie(onto, vc)                               # c∈S ⇒ (∃t)(t∈PB et c=Card seg t)

    # per-c : c∈S ⊢ ¬(PB=∅)
    Hc = N.assume(appartient(vc, vS))                          # c∈S
    ex_t = N.modus_ponens(Hc, onto_c)                          # (∃t)(t∈PB et c=Card seg t)
    # per-t : ( t∈PB et c=Card seg t ) ⊢ ¬(PB=∅)
    corps_t = et(appartient(vt, PB), egal(vc, cardinal(seg(Ro, a, vt))))
    Ht = N.assume(corps_t)
    t_in_PB = conjonction_elim_gauche(Ht)                      # t∈PB
    # PB=∅ ⊢ t∈∅ : Leibniz (PB=∅) sur Φ[w]=t∈w
    Heq = N.assume(egal(PB, E.VIDE))                           # PB=∅
    t_in_vide = _leib_transport(PB, E.VIDE, Heq,
                                lambda w: appartient(vt, w), t_in_PB)  # t∈∅
    not_t_vide = _vide_sans_element_t(vt)                      # ¬(t∈∅)
    falso = _ex_falso(t_in_vide, not_t_vide, non(egal(PB, E.VIDE)))    # ¬(PB=∅) [PB=∅,…]
    not_PB_vide = _refute_self(N.loi_deduction(egal(PB, E.VIDE), falso))  # ¬(PB=∅) [t∈PB,…]
    body_t = N.loi_deduction(corps_t, not_PB_vide)
    not_from_t = N.modus_ponens(ex_t, existe_elimination(body_t, tn))   # ¬(PB=∅) [c∈S,…]
    body_c = N.loi_deduction(appartient(vc, vS), not_from_t)
    not_from_c = N.modus_ponens(ex_c, existe_elimination(body_c, cn))   # ¬(PB=∅) [S≠∅,…]
    res = not_from_c
    assert res.conclusion == non(egal(PB, E.VIDE)), "PB≠∅ mal formé"
    return res


def _vide_sans_element_t(t):
    """⊢ ¬(t∈∅)  pour un TERME t."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)
    return instancie(ax, _t(t))


def _leib_transport(a, b, h_ab, phi_fun, h_phi_a):
    """De ⊢ a=b [h_ab] et ⊢ Φ[a] [h_phi_a] déduit ⊢ Φ[b]  (Leibniz via S6)."""
    va, vb = _t(a), _t(b)
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, _HOLE, phi_fun(var(_HOLE))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


def _ex_falso(thm_a, thm_na, z):
    """Γ⊢A, Δ⊢¬A ⟹ Γ∪Δ⊢Z  (ex falso : ¬A ⇒ (A ⇒ Z), S2)."""
    a = thm_a.conclusion
    return N.modus_ponens(thm_a, N.modus_ponens(thm_na, N.s2(non(a), z)))


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P.  ((P⇒¬P) ≡ (¬P∨¬P)→¬P par S1.)"""
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE — le CORPS du ∀S de hyp_transport_ordinal, sous hyps HONNÊTES.
# ════════════════════════════════════════════════════════════════════════════
def hyp_transport_corps_preuve(a="a", Ro="Ro", S="S"):
    """⊢ { S⊂[0,a],  S≠∅,  (∀c) realisation_segment(Ro,a,c) }
            ⊢ ( pullback(a,Ro,S)⊂a  et  pullback(a,Ro,S)≠∅  et  INTO  et  ONTO ),

    soit le CORPS du conjoint ∀S de hyp_transport_ordinal pour un S fixé (forme
    associative ((( PB⊂a et PB≠∅ ) et INTO ) et ONTO), comme _corps_Ro).

    🎯 ASSEMBLE pullback_inclus_a (CLOS) + pullback_non_vide + pullback_into (CLOS) +
    pullback_onto, sous les hypothèses HONNÊTES { S⊂[0,a], S≠∅, realisation_segment }.
    Le conjoint bo(Ro,a) de hyp_transport_ordinal N'Y FIGURE PAS : il est superflu pour
    le CORPS (INTO/⊂a/ONTO/≠∅ ne dépendent QUE de la sélection + réalisation).  theorie=22."""
    PB = pullback(a, Ro, S)
    # binders canoniques de hyp_transport_ordinal (cf. _BM/_BC/_BX/_BT du module cible)
    pb_sub = pullback_inclus_a(a, Ro, S)                       # PB⊂a            [CLOS]
    pb_ne = pullback_non_vide(a, Ro, S)                        # PB≠∅            [S⊂[0,a],S≠∅,real]
    into = pullback_into(a, Ro, S, BOIO._BT)                   # INTO            [CLOS], binder tt
    onto = pullback_onto(a, Ro, S, BOIO._BC, BOIO._BX)         # ONTO            [S⊂[0,a],real]
    g2 = conjonction_intro(pb_sub, pb_ne)                      # ( PB⊂a et PB≠∅ )
    g1 = conjonction_intro(g2, into)                           # ( … et INTO )
    corps = conjonction_intro(g1, onto)                        # ( … et ONTO )
    return corps


def hyp_transport_corps_cible(a="a", Ro="Ro", S="S"):
    """ÉNONCÉ-cible (test miroir) du CORPS du ∀S :
        ((( PB⊂a et PB≠∅ ) et INTO ) et ONTO)."""
    PB = pullback(a, Ro, S)
    return et(et(et(inclus(PB, _t(a)), non(egal(PB, E.VIDE))),
                 BOIO.hyp_realisation_min(Ro, a, S, PB, BOIO._BT)),
              BOIO.hyp_realisation_onto(Ro, a, S, PB, BOIO._BC, BOIO._BX))


def hyp_transport_prop_all_S_preuve(a="a", Ro="Ro", S="S"):
    """⊢ { (∀c) realisation_segment(Ro,a,c) }
            ⊢ (∀S)( ( S⊂[0,a] et S≠∅ ) ⇒
                    ( PB⊂a et PB≠∅ et INTO et ONTO ) ).

    🎯 LE CONJOINT « ∀S » de hyp_transport_ordinal, ENTIÈREMENT DÉRIVÉ du SEUL maillon
    RÉALISATION.  Pour chaque S : déchargeur ( S⊂[0,a] et S≠∅ ) sur hyp_transport_corps_
    preuve (qui livre le corps), puis généralisation sur S.  Conclusion == la 2e
    composante de _corps_Ro (test miroir).  theorie=22, NON vacueux."""
    interv = intervalle_0a(a)
    vS = _t(S)
    corps = hyp_transport_corps_preuve(a, Ro, S)               # [S⊂[0,a], S≠∅, real]
    HsS = et(inclus(vS, interv), non(egal(vS, E.VIDE)))
    H = N.assume(HsS)
    sub = conjonction_elim_gauche(H)                           # S⊂[0,a]
    ne = conjonction_elim_droite(H)                            # S≠∅
    c2 = N.modus_ponens(sub, N.loi_deduction(inclus(vS, interv), corps))
    c2 = N.modus_ponens(ne, N.loi_deduction(non(egal(vS, E.VIDE)), c2))   # corps [HsS, real]
    body_imp = N.loi_deduction(HsS, c2)                        # HsS ⇒ corps_S
    return N.generalisation(S, body_imp)                      # (∀S)(…)  [real]


def bo_form_artefact(a="a", Ro="Ro", S="S"):
    """Le conjoint est_bien_ordonne(Ro,a) tel que hyp_transport_ordinal le DÉPOSE :
    `_bo_form_canon(a,Ro,pullback(a,Ro,S),_BM,_BX)`.

    ⚠️ FORMULE DÉGÉNÉRÉE : le slot du LIANT « X » de est_bien_ordonne y est occupé
    par le TERME COMPOSÉ pullback(a,Ro,S) (= pullback_seg_card(a,Ro,S)).  AUCUNE règle
    du noyau ne peut PRODUIRE un liant-terme (generalisation/s5/alpha_existe ne lient
    que des NOMS de variable) ⇒ ce conjoint ne peut qu'être ASSUMÉ, jamais dérivé.
    C'est l'OBSTACLE STRUCTUREL au `==` exact (cf. docstring du module)."""
    PB = pullback(a, Ro, S)
    return BOIO._bo_form_canon(a, Ro, PB, BOIO._BM, BOIO._BX)


def hyp_transport_ordinal_preuve(a="a", Ro="Ro", S="S"):
    """⊢ { bo_form_artefact(a,Ro,S),  (∀c) realisation_segment(Ro,a,c) }
            ⊢ hyp_transport_ordinal(a)    (conclusion == la cible LITTÉRALEMENT).

    🎯 LE TRANSPORT, ASSEMBLÉ AU MAXIMUM.  La conclusion est EXACTEMENT
    hyp_transport_ordinal(a) (test miroir `==`).  Les 4 conjoints du pullback (⊂a, ≠∅,
    INTO, ONTO) et l'élimination/introduction du ∃Ro sont TOUS dérivés.  Il ne SUBSISTE
    que DEUX hypothèses HONNÊTES, JAMAIS postulées :

      (1) (∀c) realisation_segment(Ro,a,c)  — le SEUL maillon mathématique : « tout
          cardinal ≤a est le cardinal d'un segment initial de (a,Ro) » (représentation
          ordinale ; cf. RAPPORT — non encore close dans le projet).

      (2) bo_form_artefact(a,Ro,S)  — la forme DÉGÉNÉRÉE est_bien_ordonne(Ro,a) que la
          DÉFINITION de hyp_transport_ordinal impose (liant-TERME pullback dans le slot
          « X ») ; structurellement NON dérivable (cf. docstring) — Zermelo donne le bon
          ordre BIEN FORMÉ, qui n'égale pas (==) cette forme dégénérée.  Reste assumé.

    Tout le reste (collectivisation S8 du pullback, INTO, ⊂a, ONTO, ≠∅, ∀S, ∃Ro) est
    DÉRIVÉ.  theorie_ensembles()=22.  NON vacueux."""
    body = BOIO._corps_Ro(a, Ro, S)                           # et(bo_form, prop_all_S)
    H_bo = N.assume(bo_form_artefact(a, Ro, S))               # bo_form (artefact, assumé)
    prop_all_S = hyp_transport_prop_all_S_preuve(a, Ro, S)    # (∀S)(…)  [real]
    body_th = conjonction_intro(H_bo, prop_all_S)             # et(bo_form, prop_all_S)
    assert body_th.conclusion == body, "corps ≠ _corps_Ro de hyp_transport_ordinal"
    res = N.modus_ponens(body_th, N.s5(body, _t(Ro), Ro))     # (∃Ro)(…)
    assert res.conclusion == BOIO.hyp_transport_ordinal(a), \
        "conclusion ≠ hyp_transport_ordinal(a) déposé"
    return res


def hyp_transport_ordinal_preuve_hypotheses(a="a", Ro="Ro", S="S"):
    """Les 2 HYPOTHÈSES SURVIVANTES ATTENDUES (test miroir) de hyp_transport_ordinal_
    preuve : { (∀c) realisation_segment(Ro,a,c),  bo_form_artefact(a,Ro,S) }."""
    return {
        pourtout(BOIO._BC, realisation_segment(Ro, a, BOIO._BC, BOIO._BX)),
        bo_form_artefact(a, Ro, S),
    }


__all__ = [
    "pullback", "axiome_pullback", "theorie_pullback", "pullback_membre",
    "pullback_into", "pullback_inclus_a",
    "realisation_segment",
    "pullback_onto", "pullback_non_vide",
    "hyp_transport_corps_preuve", "hyp_transport_corps_cible",
    "hyp_transport_prop_all_S_preuve",
    "bo_form_artefact",
    "hyp_transport_ordinal_preuve", "hyp_transport_ordinal_preuve_hypotheses",
]
