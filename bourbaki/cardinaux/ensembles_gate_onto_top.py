"""§III.4 — FERMETURE INCONDITIONNELLE du GATE ℕ #1 : `bon_ordre_intervalle(a)` et
`cardinaux_bien_ordonnes(a)` CLOS (0 hypothèse résiduelle).

────────────────────────────────────────────────────────────────────────────────
LE POINT UNIQUE CORRIGÉ.

`ensembles_realisation_segment_close.realisation_garde_depuis_subset` dérive la
réalisation gardée `(∀c)( est_cardinal(c) ⇒ realisation_segment(Ro,a,c) )` en
appliquant `subset_realise_segment(B)` (B=image(F,c)) pour TOUT cardinal c≤a.  Or
`subset_realise_segment` est FAUX au cardinal TOP c=Card(a) : il exigerait que
B≁a soit équipotent à un segment PROPRE, impossible quand B épuise a (cf. la
docstring de ensembles_subset_realise_close — `realise_segment_pour_B_clean` n'est
clos que sous `¬Eq(B,a)`).  C'est l'UNIQUE maillon faux de toute la chaîne.

LA CORRECTION (ce module, sans MODIFIER aucun fichier).  On REMPLACE l'application
de `subset_realise_segment` par le théorème CLOS `realise_segment_pour_B_clean`
(`{bo(Ro,a), B⊆a, ¬Eq(B,a)} ⊢ (∃t)(t∈a et Eq(B,seg(a,Ro,t)))`).  La réalisation
gardée DEVIENT donc GARDÉE PAR ¬Eq(c,Card a) (puisque Card B=c, ¬Eq(B,a) ⟺ ¬Eq(c,Card a)) :

    realisation_segment_garde_clean(Ro,a) :=
        (∀c)( ( est_cardinal(c) et ¬Eq(c,Card a) ) ⇒ realisation_segment(Ro,a,c) ).

VRAIE et CLOSE sous { bo(Ro,a) }.  Le cardinal TOP c=Card(a) (le SEUL où la
réalisation par segment propre échoue) est EXCLU de la garde, et traité SÉPARÉMENT
par un CASE-SPLIT order-théorique : Card(a) est le ≤-MAX de [0,a], donc

  • soit S possède un élément ≠ Card(a)  (S' := S∖{Card a} ≠ ∅) : le min de S vit
    dans S' (Card a, étant le max, n'est jamais le min quand S'≠∅) ; on l'extrait du
    pullback restreint à ¬Eq(c,Card a) (`clause_min_clean`, qui couvre S' par l'onto
    CLEAN et borne le top par µ≤Card a via le transport µ≤a + Card µ=µ) ;
  • soit ∀c∈S, c=Card(a)  (S={Card a}) : min(S)=Card(a) par RÉFLEXIVITÉ de ≤.

LE GATE ℕ devient alors INCONDITIONNEL : `bo(Ro,a)` est déchargé par ZERMELO
(`zermelo`, CLOS), donc `bon_ordre_intervalle(a)` et `cardinaux_bien_ordonnes(a)`
sont CLOS (0 hypothèse).

INVARIANT : theorie_ensembles() = 22.  RIEN POSTULÉ : le cas TOP est PROUVÉ
(singleton/réflexivité), JAMAIS assumé.  On CLONE les fonctions déposées (sans les
éditer) en y substituant le seul maillon faux par sa version close.
"""
from __future__ import annotations

from functools import lru_cache

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, appartient, existe, pourtout, inclus, tau,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere, contraposition, syllogisme, cas,
    tiers_exclu, antecedent_consequent,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    composer_egalites, symetrie as _sym_eq,
)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_injection_de, equipotent, inf_egal_card, cardinal, est_cardinal,
)
from bourbaki.cardinaux.ensembles_segments_construction import seg, _R_de
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import (
    cardinal_egal_si_equipotent, equipotent_si_cardinal_egal,
)
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    _cardinal_est_son_cardinal, _cardinal_idempotent_t,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    ZERO, intervalle_0a, ordre_induit_intervalle, bon_ordre_intervalle,
    cardinaux_bien_ordonnes_de_bon_ordre,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal_ordre import (
    relation_ordre_dans_intervalle,
)
from bourbaki.entiers.ensembles_recurrence_C61 import cardinaux_bien_ordonnes

import bourbaki.cardinaux.ensembles_hyp_transport_ordinal_preuve as HTP
import bourbaki.cardinaux.ensembles_bon_ordre_intervalle_ordinal as BOIO
import bourbaki.cardinaux.ensembles_realisation_segment_preuve as RSP
import bourbaki.cardinaux.ensembles_realisation_segment_close as RSC
import bourbaki.cardinaux.ensembles_subset_realise_close as SC
import bourbaki.ordre.ensembles_zermelo as Z


def _t(t):
    return t if isinstance(t, Terme) else var(t)


_HOLE = "hole_gate_top"

# ── binders ──────────────────────────────────────────────────────────────────
#   cardinal binder FRESH (avoids collision with the internal binders 'a','x','w','z'
#   of realise_segment_pour_B_clean's proof machinery when B=image(F,c)).
_CFRESH = "cgate"
#   FINAL segment-witness binder of the realisation (≠ 'x','m','cgate' — 'x' is the
#   clause-comparison binder of bon_ordre_intervalle, 'm' the min-element binder).
_LIT_T = "tw"
#   TRANSIENT witness binder of realise_segment_pour_B_clean's existential.
_TWIT = "x"


# ════════════════════════════════════════════════════════════════════════════
#  helpers TERME-niveau (Prop 1 deux sens ; aux TERMES, jamais var() sur un Terme).
# ════════════════════════════════════════════════════════════════════════════
def _card_eq_si_eq(u, v):
    """⊢ Eq(u,v) ⇒ ( Card u = Card v )  aux TERMES u,v  (cardinal_egal_si_equipotent)."""
    gen = N.generalisation("Xq", N.generalisation("Yq", cardinal_egal_si_equipotent("Xq", "Yq")))
    return instancie(instancie(gen, _t(u)), _t(v))


def _eq_si_card_eq(u, v):
    """⊢ ( Card u = Card v ) ⇒ Eq(u,v)  aux TERMES u,v  (equipotent_si_cardinal_egal)."""
    gen = N.generalisation("Xr", N.generalisation("Yr", equipotent_si_cardinal_egal("Xr", "Yr")))
    return instancie(instancie(gen, _t(u)), _t(v))


def _est_cardinal_de_interv(a, c):
    """⊢ ( c ∈ [0,a] ) ⇒ est_cardinal(c)  ([0,a])."""
    return RSC._est_cardinal_de_interv(a, c)


def _transporte_card(u, v):
    """⊢ ( u ≤ v ) ⇒ ( Card u ≤ Card v )  aux TERMES u,v  (inf_egal_transporte_cardinal)."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale_props_exposant_monotone import (
        inf_egal_transporte_cardinal,
    )
    gen = N.generalisation("Xtc", N.generalisation("Ytc",
        inf_egal_transporte_cardinal("Xtc", "Ytc")))
    return instancie(instancie(gen, _t(u)), _t(v))


# ════════════════════════════════════════════════════════════════════════════
#  1️⃣  réalisation gardée CLEAN — dérivée de realise_segment_pour_B_clean (CLOS).
# ════════════════════════════════════════════════════════════════════════════
def realisation_segment_garde_clean(Ro="Ro", a="a", c=_CFRESH, t=_LIT_T):
    """ÉNONCÉ — la réalisation gardée par ¬Eq(c,Card a) (VRAIE, à l'exclusion du top) :

        (∀c)( ( est_cardinal(c) et ¬Eq(c,Card a) ) ⇒ realisation_segment(Ro,a,c) )."""
    cn = c if isinstance(c, str) else c.nom
    vc = var(cn)
    return pourtout(cn, impl(et(est_cardinal(vc), non(equipotent(vc, cardinal(_t(a))))),
                             HTP.realisation_segment(Ro, a, cn, t)))


@lru_cache(maxsize=None)
def _realise_clean_generalized(Ro="Ro"):
    """⊢ (∀asr)(∀Bsr)( bo(Ro,asr) ⇒ ( Bsr⊆asr ⇒ ( ¬Eq(Bsr,asr) ⇒
            (∃x)( x∈asr et Eq(Bsr, seg(asr,Ro,x)) ) ) ) ).   CLOSED.

    ⚠️ MÉMOÏSÉ (lru_cache) : `realise_segment_pour_B_clean` est coûteux ; cette version
    GÉNÉRIQUE (CLOSED) est construite 1× par nom Ro et réutilisée (amortissement).

    🎯 `realise_segment_pour_B_clean` aux NOMS GÉNÉRIQUES (asr, Bsr) : ses 3 hyps
    {bo, B⊆a, ¬Eq(B,a)} déchargées (bo externe), CLOS, puis généralisé sur Bsr et asr.
    Permet d'instancier au TERME COMPLEXE B=image(F,c) SANS capture (les binders internes
    de la preuve — le 'a' du min de bo, les 'x','w','z' de l'iso — sont au-dessous du ∀,
    `instancie` substitue de façon capture-évitante)."""
    aN, BN = "asr", "Bsr"
    vaN, vBN = var(aN), var(BN)
    rspbc = SC.realise_segment_pour_B_clean(Ro, aN, BN)   # {bo, B⊆a, ¬Eq(B,a)} ⊢ concl
    bo_f = E.est_bien_ordonne(_R_de(Ro), vaN)
    sub_f = inclus(vBN, vaN)
    neq_f = non(equipotent(vBN, vaN))
    assert set(rspbc.hypotheses) == {bo_f, sub_f, neq_f}, \
        f"hyps de realise_segment_pour_B_clean inattendues: {rspbc.hypotheses}"
    imp = N.loi_deduction(neq_f, rspbc)                   # ¬Eq ⇒ concl      [bo, B⊆a]
    imp = N.loi_deduction(sub_f, imp)                     # B⊆a ⇒ (¬Eq ⇒ concl)  [bo]
    imp = N.loi_deduction(bo_f, imp)                      # bo ⇒ (...)   CLOSED
    assert imp.est_clos, "imp non clos avant généralisation"
    g = N.generalisation(BN, imp)
    g = N.generalisation(aN, g)
    return g


def realisation_garde_clean(Ro="Ro", a="a", c=_CFRESH, t=_LIT_T):
    """⊢ { bo(Ro,a) }  ⊢  realisation_segment_garde_clean(Ro,a).

    🎯 CLONE de `realisation_garde_depuis_subset`, avec l'application FAUSSE de
    `subset_realise_segment(B)` REMPLACÉE par le CLOS `realise_segment_pour_B_clean`
    (via _realise_clean_generalized, instancié à B=image(F,c)).  La garde DEVIENT
    `est_cardinal(c) et ¬Eq(c,Card a)` : ¬Eq(B,a) (requis par realise_..._clean) se
    dérive de ¬Eq(c,Card a) car Card B = Card c = c (purement au niveau CARDINAL, sans
    equipotence_transitive sur le terme complexe B).  L'hypothèse `bo(Ro,a)` SURVIT —
    HONNÊTE, déchargée par Zermelo dans le GATE.  theorie=22, NON vacueux."""
    va, vc = _t(a), var(c)
    tn = t if isinstance(t, str) else t.nom    # FINAL realisation witness binder
    twit = _TWIT                               # transient witness binder of realise_..._clean
    vtw = var(twit)
    inj_F = est_injection_de(var("F"), vc, va)

    # témoin F de c≤a, B := image(F,c), B⊆a, Eq(c,B)
    Hle = N.assume(inf_egal_card(vc, va))
    wit = N.modus_ponens(Hle, N.existe_temoin(inj_F, "F"))
    Ft = tau("F", inj_F)
    B = E.image(Ft, vc)
    B_sub_a = conjonction_elim_droite(wit)                          # image(τF,c) ⊂ a
    eq_cB = N.modus_ponens(wit, RSC.injection_donne_equipotent_image(Ft, vc, va))   # Eq(c,B)

    # garde : est_cardinal(c) et ¬Eq(c,Card a)
    H_card = N.assume(est_cardinal(vc))
    H_neq = N.assume(non(equipotent(vc, cardinal(va))))             # ¬Eq(c, Card a)

    # Card c = c (garde) et Card c = Card B
    cc_eq_c = N.modus_ponens(H_card, _cardinal_est_son_cardinal(vc))   # Card c = c
    cardC_eq_B = N.modus_ponens(eq_cB, _card_eq_si_eq(vc, B))          # Card c = Card B

    # ¬Eq(B,a) à partir de ¬Eq(c,Card a), PUREMENT au niveau CARDINAL :
    #   Eq(B,a) ⇒ Card B = Card a   (Prop 1 direct)
    imp_BA_card = _card_eq_si_eq(B, va)
    #   Card B = Card a ⇒ Eq(c, Card a)  via Card c = Card B = Card a = Card(Card a)
    H_cardBA = N.assume(egal(cardinal(B), cardinal(va)))
    cardc_eq_carda = composer_egalites(cardC_eq_B, H_cardBA)          # Card c = Card a
    cardcarda_eq_carda = _cardinal_idempotent_t(va)                  # Card(Card a) = Card a
    carda_eq_cardcarda = N.modus_ponens(cardcarda_eq_carda,
        _sym_eq(cardinal(cardinal(va)), cardinal(va)))               # Card a = Card(Card a)
    cardc_eq_cardcarda = composer_egalites(cardc_eq_carda, carda_eq_cardcarda)
    eq_c_carda = N.modus_ponens(cardc_eq_cardcarda, _eq_si_card_eq(vc, cardinal(va)))  # Eq(c,Card a)
    imp_cardBA = N.loi_deduction(egal(cardinal(B), cardinal(va)), eq_c_carda)
    imp_Ba = syllogisme(imp_BA_card, imp_cardBA)                     # Eq(B,a) ⇒ Eq(c,Card a)
    contra = contraposition(imp_Ba)                                 # ¬Eq(c,Card a) ⇒ ¬Eq(B,a)
    not_eq_Ba = N.modus_ponens(H_neq, contra)                       # ¬Eq(B,a)

    # realise_segment_pour_B_clean GÉNÉRIQUE instancié aux TERMES a, B
    gen = _realise_clean_generalized(Ro)
    inst = instancie(instancie(gen, va), B)
    bo_form, _ = antecedent_consequent(inst.conclusion)             # bo(Ro,a) forme exacte
    H_bo = N.assume(bo_form)
    step1 = N.modus_ponens(H_bo, inst)
    step2 = N.modus_ponens(B_sub_a, step1)
    ex_t = N.modus_ponens(not_eq_Ba, step2)                         # (∃x)(x∈a ∧ Eq(B,seg))

    # per-témoin (binder transitoire « x » de realise_..._clean) :
    #   ( x∈a et Eq(B,seg(a,Ro,x)) ) ⊢ ( x∈a et Card(seg(a,Ro,x))=c )
    segt = seg(Ro, va, vtw)
    corps_t = et(appartient(vtw, va), equipotent(B, segt))
    Ht = N.assume(corps_t)
    t_in_a = conjonction_elim_gauche(Ht)
    eq_B_seg = conjonction_elim_droite(Ht)
    cardB_eq_seg = N.modus_ponens(eq_B_seg, _card_eq_si_eq(B, segt))   # Card B = Card seg
    cardC_eq_seg = composer_egalites(cardC_eq_B, cardB_eq_seg)         # Card c = Card seg
    c_eq_cardC = N.modus_ponens(cc_eq_c, _sym_eq(cardinal(vc), vc))    # c = Card c
    c_eq_seg = composer_egalites(c_eq_cardC, cardC_eq_seg)            # c = Card seg
    cardseg_eq_c = N.modus_ponens(c_eq_seg, _sym_eq(vc, cardinal(segt)))   # Card seg = c

    inst_body = et(appartient(vtw, va), egal(cardinal(segt), vc))     # instance à witness x
    body = conjonction_intro(t_in_a, cardseg_eq_c)
    assert body.conclusion == inst_body, "corps réalisation mal formé"
    # RE-INTRODUIRE (∃tn) [tn='tw'] : r = corps avec var(tn), témoin = var(twit)
    vt = var(tn)
    real_body_tn = et(appartient(vt, va), egal(cardinal(seg(Ro, va, vt)), vc))
    ex_concl = N.modus_ponens(body, N.s5(real_body_tn, vtw, tn))      # (∃tn) real_body_tn
    body_imp = N.loi_deduction(corps_t, ex_concl)
    real_concl = N.modus_ponens(ex_t, existe_elimination(body_imp, twit))

    real_seg = N.loi_deduction(inf_egal_card(vc, va), real_concl)  # realisation_segment(Ro,a,c)
    # décharger la garde ( est_cardinal(c) et ¬Eq(c,Card a) )
    guard_form = et(est_cardinal(vc), non(equipotent(vc, cardinal(va))))
    H_guard = N.assume(guard_form)
    real2 = N.modus_ponens(conjonction_elim_gauche(H_guard),
                           N.loi_deduction(est_cardinal(vc), real_seg))
    real3 = N.modus_ponens(conjonction_elim_droite(H_guard),
                           N.loi_deduction(non(equipotent(vc, cardinal(va))), real2))
    guarded_body = N.loi_deduction(guard_form, real3)
    res = N.generalisation(c, guarded_body)
    assert res.conclusion == realisation_segment_garde_clean(Ro, a, c, t), \
        "conclusion ≠ realisation_segment_garde_clean"
    return res


def _bo_form_clean(Ro="Ro", a="a"):
    """La FORME EXACTE de bo(Ro,a) portée par realisation_garde_clean : extraite de
    `_realise_clean_generalized` instancié au TERME `a` (de sorte qu'elle coïncide
    EXACTEMENT avec l'hypothèse, y compris la canonicalisation éventuelle du liant
    min-élément quand le nom d'ensemble `a` entre en collision avec lui).  Pour un
    nom d'ensemble ≠ 'a' (cf. _AINT='agate'), c'est est_bien_ordonne par défaut."""
    gen = _realise_clean_generalized(Ro)
    inst = instancie(instancie(gen, _t(a)), var("Bdummy_boform"))
    bo_form, _ = antecedent_consequent(inst.conclusion)
    return bo_form


# ════════════════════════════════════════════════════════════════════════════
#  ZERMELO PARAMÉTRIQUE — décharge d'une forme bo(Ro,a) à binders min-clause donnés.
#  (clone PARAMÉTRIQUE de RSP._bo_full_equiv / RSP.zermelo_bo_form.)
# ════════════════════════════════════════════════════════════════════════════
def _bo_alpha_equiv(Rname, e, setb, elemb, compb):
    """⊢ est_bien_ordonne(_R_de(R), e, X='S', a='a', w='w')
          ⇔ est_bien_ordonne(_R_de(R), e, X=setb, a=elemb, w=compb).

    α-renomme les TROIS liants de la clause-minimum (∀S→∀setb, ∃a→∃elemb, ∀w→∀compb).
    Renommage innermost-first (w, a, S).  Clone PARAMÉTRIQUE de RSP._bo_full_equiv."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        alpha_pour_tout, alpha_existe, congruence_pour_tout, congruence_existe,
    )
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        et_congruence_droite, equivalence_transitivite, ou_congruence,
    )
    from bourbaki.ensembles.ensembles_abrege import est_relation_ordre_dans
    Rf = _R_de(Rname)
    ve = _t(e)
    vS = var("S")
    eq_refl = lambda f: conjonction_intro(a_implique_a(f), a_implique_a(f))   # f ⇔ f
    impl_cong_d = lambda A, thm_eq: ou_congruence(eq_refl(non(A)), thm_eq)

    # ── w → compb  (identité si compb=='w')
    forallw_w = pourtout("w", impl(appartient(var("w"), vS), Rf(var("a"), var("w"))))
    if compb == "w":
        eq_petit = eq_refl(et(appartient(var("a"), vS), forallw_w))
        body_a_comp = et(appartient(var("a"), vS), forallw_w)
    else:
        eq_forallw = alpha_pour_tout("w", compb,
            impl(appartient(var("w"), vS), Rf(var("a"), var("w"))))
        eq_pb = et_congruence_droite(appartient(var("a"), vS), eq_forallw)
        eq_petit = eq_pb
        body_a_comp = et(appartient(var("a"), vS),
            pourtout(compb, impl(appartient(var(compb), vS), Rf(var("a"), var(compb)))))

    # ── a → elemb  (identité si elemb=='a')
    if elemb == "a":
        eq_ex = congruence_existe(eq_petit, "a")
    else:
        eq_ex = equivalence_transitivite(congruence_existe(eq_petit, "a"),
                                         alpha_existe("a", elemb, body_a_comp))
    CS = et(inclus(vS, ve), non(egal(vS, E.VIDE)))
    eq_forallS = congruence_pour_tout(impl_cong_d(CS, eq_ex), "S")
    petit_e_c = existe(elemb, et(appartient(var(elemb), vS),
        pourtout(compb, impl(appartient(var(compb), vS), Rf(var(elemb), var(compb))))))

    # ── S → setb  (identité si setb=='S')
    if setb == "S":
        eq_minclause = eq_forallS
    else:
        eq_minclause = equivalence_transitivite(eq_forallS,
            alpha_pour_tout("S", setb, impl(CS, petit_e_c)))
    return et_congruence_droite(est_relation_ordre_dans(Rf, ve), eq_minclause)


def _zermelo_bo(a, setb, elemb, compb, Ro="Ro"):
    """⊢ (∃Ro) est_bien_ordonne(_R_de(Ro), a, X=setb, a=elemb, w=compb).   CLOS.

    🎯 ZERMELO (CLOS) α-renommé aux binders min-clause (setb, elemb, compb).  Clone
    PARAMÉTRIQUE de RSP.zermelo_bo_form : zermelo('Xz') donne (∃Rz) bo(.., S,a,w) ; on
    α-renomme la clause-minimum (S→setb, a→elemb, w→compb), renomme ∃Rz→Ro, généralise
    Xz et instancie au TERME a.  CLOS, 0 hypothèse."""
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
        alpha_existe, congruence_existe,
    )
    va = _t(a)
    Ron = Ro if isinstance(Ro, str) else Ro.nom
    z = Z.zermelo("Xz", "Mz", "Rz")                 # (∃Rz) bo(_R_de Rz, Xz, S,a,w)  CLOS
    z2 = N.modus_ponens(z, equivalence_avant(
        congruence_existe(_bo_alpha_equiv("Rz", "Xz", setb, elemb, compb), "Rz")))
    z3 = N.modus_ponens(z2, equivalence_avant(
        alpha_existe("Rz", Ron,
            E.est_bien_ordonne(_R_de("Rz"), var("Xz"), X=setb, a=elemb, w=compb))))
    res = instancie(N.generalisation("Xz", z3), va)
    assert res.conclusion == existe(Ron,
        E.est_bien_ordonne(_R_de(Ron), va, X=setb, a=elemb, w=compb)), \
        "_zermelo_bo ≠ (∃Ro) bo(Ro,a) [binders donnés]"
    return res


def _zermelo_bo_clean(a="a", Ro="Ro"):
    """⊢ (∃Ro) bo_clean(Ro,a)   où bo_clean = la forme EXACTE portée par realisation_garde_clean.
    Décharge l'hypothèse `bo` de realisation_garde_clean.  Binders min-clause EXTRAITS de
    _bo_form_clean (robuste à toute canonicalisation de liant).  CLOS."""
    setb, elemb, compb = _bo_min_binders(_bo_form_clean(Ro, a))
    z = _zermelo_bo(a, setb, elemb, compb, Ro)
    Ron = Ro if isinstance(Ro, str) else Ro.nom
    assert z.conclusion == existe(Ron, _bo_form_clean(Ro, a)), \
        "_zermelo_bo_clean ≠ (∃Ro) bo_clean (forme exacte)"
    return z


def _equiv_clean_pp(Ro="Ro", a="a"):
    """⊢ bo_clean(Ro,a) ⇔ bo_pp(Ro,a).   CLOS (α-équivalence : mêmes binders à renommage près).

    bo_clean = est_bien_ordonne(.., X='X',a='a',w='w') (de realisation_garde_clean) ;
    bo_pp = la forme GENUINE de plus_petit_card_segment (binders extraits structurellement).
    Composition : (bo_Saw ⇔ bo_clean)⁻¹ puis (bo_Saw ⇔ bo_pp)."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import (
        equivalence_symetrie, equivalence_transitivite,
    )
    setb, elemb, compb = _bo_min_binders(_bo_form_pp(Ro, a))
    e_clean = _bo_alpha_equiv(Ro, a, "X", "a", "w")            # bo_Saw ⇔ bo_clean
    e_pp = _bo_alpha_equiv(Ro, a, setb, elemb, compb)          # bo_Saw ⇔ bo_pp
    return equivalence_transitivite(equivalence_symetrie(e_clean), e_pp)   # bo_clean ⇔ bo_pp


# ════════════════════════════════════════════════════════════════════════════
#  2️⃣  ONTO CLEAN — couvre c∈S avec ¬Eq(c,Card a)  (le pullback couvre S∖{top}).
# ════════════════════════════════════════════════════════════════════════════
def pullback_onto_clean(a="a", Ro="Ro", S="S", c=_CFRESH, t=_LIT_T):
    """⊢ { S⊂[0,a],  realisation_segment_garde_clean(Ro,a) }
            ⊢ (∀c)( ( c∈S et ¬Eq(c,Card a) ) ⇒ (∃t)( t∈pullback(a,Ro,S) et c=Card(seg(a,Ro,t)) ) ).

    🎯 CLONE de `pullback_onto_garde`, consommant la réalisation CLEAN (gardée par
    ¬Eq(c,Card a)).  Pour c∈S avec ¬Eq(c,Card a) : c∈[0,a] (S⊂[0,a]) ⇒ est_cardinal(c)
    et c≤a ; la garde `est_cardinal(c) et ¬Eq(c,Card a)` est DÉCHARGÉE (est_cardinal de
    c∈[0,a] ; ¬Eq de la condition de branche).  La réalisation donne t∈a avec
    Card(seg t)=c, donc Card(seg t)∈S ⇒ t∈PB, et c=Card(seg t).  Le pullback PB est le
    MÊME que celui déposé (`HTP.pullback`).  theorie=22, NON vacueux."""
    cn = c if isinstance(c, str) else c.nom
    tn = t if isinstance(t, str) else t.nom
    vc, vt = var(cn), var(tn)
    va, vS = _t(a), _t(S)
    PB = HTP.pullback(a, Ro, S)
    carda = cardinal(va)

    H_realg = N.assume(realisation_segment_garde_clean(Ro, a, cn, tn))
    cond = et(appartient(vc, vS), non(equipotent(vc, carda)))        # c∈S et ¬Eq(c,Card a)
    Hcond = N.assume(cond)
    Hc = conjonction_elim_gauche(Hcond)                             # c∈S
    H_neq = conjonction_elim_droite(Hcond)                          # ¬Eq(c,Card a)
    c_interv = N.modus_ponens(Hc, HTP._inclus_S_interv(a, S, vc))   # c∈[0,a]
    c_le_a = HTP._c_le_a(a, vc, c_interv)                           # c ≤ a
    est_card_c = N.modus_ponens(c_interv, _est_cardinal_de_interv(a, vc))   # est_cardinal(c)
    guard = conjonction_intro(est_card_c, H_neq)                    # est_cardinal(c) et ¬Eq(c,Card a)
    real_c = N.modus_ponens(guard, instancie(H_realg, vc))          # c≤a ⇒ (∃t)…
    ex_t = N.modus_ponens(c_le_a, real_c)                          # (∃t)( t∈a et Card seg=c )

    cardseg = cardinal(seg(Ro, a, vt))
    corps_t = et(appartient(vt, va), egal(cardseg, vc))
    Ht = N.assume(corps_t)
    t_in_a = conjonction_elim_gauche(Ht)
    eq_cardseg_c = conjonction_elim_droite(Ht)
    c_eq_cardseg = HTP._sym(cardseg, vc, eq_cardseg_c)             # c = Card(seg t)
    cardseg_in_S = HTP._leib_transport(vc, cardseg, c_eq_cardseg,
                                       lambda w: appartient(w, vS), Hc)   # Card(seg)∈S
    corps_membre = conjonction_intro(t_in_a, cardseg_in_S)
    t_in_PB = N.modus_ponens(corps_membre, equivalence_arriere(HTP.pullback_membre(a, Ro, S, tn)))
    cible_corps = conjonction_intro(t_in_PB, c_eq_cardseg)
    body_ex = et(appartient(vt, PB), egal(vc, cardseg))
    assert cible_corps.conclusion == body_ex, "corps ONTO clean mal formé"
    ex_intro = N.modus_ponens(cible_corps, N.s5(body_ex, vt, tn))
    wit_imp = N.loi_deduction(corps_t, ex_intro)
    ex_from = N.modus_ponens(ex_t, existe_elimination(wit_imp, tn))
    res = N.generalisation(cn, N.loi_deduction(cond, ex_from))
    assert res.conclusion == pullback_onto_clean_cible(a, Ro, S, cn, tn), \
        "pullback_onto_clean ≠ cible"
    return res


def pullback_onto_clean_cible(a="a", Ro="Ro", S="S", c=_CFRESH, t=_LIT_T):
    """ÉNONCÉ-cible (test miroir) de pullback_onto_clean."""
    cn = c if isinstance(c, str) else c.nom
    tn = t if isinstance(t, str) else t.nom
    vc, vt = var(cn), var(tn)
    va, vS = _t(a), _t(S)
    PB = HTP.pullback(a, Ro, S)
    cardseg = cardinal(seg(Ro, a, vt))
    return pourtout(cn, impl(et(appartient(vc, vS), non(equipotent(vc, cardinal(va)))),
                             existe(tn, et(appartient(vt, PB), egal(vc, cardseg)))))


# ════════════════════════════════════════════════════════════════════════════
#  PB ≠ ∅ depuis la condition de branche  ( ∃c∈S, ¬Eq(c,Card a) ).
# ════════════════════════════════════════════════════════════════════════════
def _S_top(a, S, c=_CFRESH):
    """ÉNONCÉ de la condition de branche « S possède un élément ≠ Card a » :
        (∃c)( c∈S et ¬Eq(c, Card a) )."""
    cn = c if isinstance(c, str) else c.nom
    vc = var(cn)
    return existe(cn, et(appartient(vc, _t(S)), non(equipotent(vc, cardinal(_t(a))))))


def pullback_non_vide_clean(a="a", Ro="Ro", S="S", c=_CFRESH, t=_LIT_T):
    """⊢ { S⊂[0,a],  realisation_segment_garde_clean(Ro,a),  (∃c)(c∈S et ¬Eq(c,Card a)) }
            ⊢ ¬( pullback(a,Ro,S) = ∅ ).

    🎯 La condition de branche `(∃c)(c∈S et ¬Eq(c,Card a))` fournit un c REALISABLE par
    l'onto CLEAN : t∈PB, donc PB=∅ donnerait t∈∅ (ex falso).  Mirror de
    `pullback_non_vide_garde` mais alimenté par l'onto CLEAN + la condition de branche
    (au lieu de S≠∅ + onto total)."""
    cn = c if isinstance(c, str) else c.nom
    tn = t if isinstance(t, str) else t.nom
    vc, vt = var(cn), var(tn)
    va, vS = _t(a), _t(S)
    PB = HTP.pullback(a, Ro, S)

    H_top = N.assume(_S_top(a, S, cn))                              # (∃c)(c∈S et ¬Eq(c,Card a))
    onto = pullback_onto_clean(a, Ro, S, cn, tn)
    onto_c = instancie(onto, vc)                                    # (c∈S et ¬Eq) ⇒ (∃t)…
    cond = et(appartient(vc, vS), non(equipotent(vc, cardinal(va))))
    Hcond = N.assume(cond)
    ex_t = N.modus_ponens(Hcond, onto_c)                           # (∃t)(t∈PB et c=Card seg)
    corps_t = et(appartient(vt, PB), egal(vc, cardinal(seg(Ro, a, vt))))
    Ht = N.assume(corps_t)
    t_in_PB = conjonction_elim_gauche(Ht)
    Heq = N.assume(egal(PB, E.VIDE))
    t_in_vide = HTP._leib_transport(PB, E.VIDE, Heq, lambda w: appartient(vt, w), t_in_PB)
    not_t_vide = HTP._vide_sans_element_t(vt)
    falso = HTP._ex_falso(t_in_vide, not_t_vide, non(egal(PB, E.VIDE)))
    not_PB_vide = HTP._refute_self(N.loi_deduction(egal(PB, E.VIDE), falso))
    body_t = N.loi_deduction(corps_t, not_PB_vide)
    not_from_t = N.modus_ponens(ex_t, existe_elimination(body_t, tn))
    body_c = N.loi_deduction(cond, not_from_t)
    res = N.modus_ponens(H_top, existe_elimination(body_c, cn))
    assert res.conclusion == non(egal(PB, E.VIDE)), "PB≠∅ clean mal formé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  ≤-min de PB via plus_petit_card_segment à la VARIABLE Tpb (bo NON dégénéré).
# ════════════════════════════════════════════════════════════════════════════
_TPB = "Tpb"


def _plus_petit_PB(Ro="Ro", a="a", S="S", m="ms", xs="xs"):
    """⊢ { bo_pp(Ro,a) }  ⊢  ( PB⊂a et PB≠∅ ) ⇒
            (∃m)( m∈PB et (∀xs)( xs∈PB ⇒ Card(seg m)≤Card(seg xs) ) )   où PB=pullback(a,Ro,S).

    🎯 `plus_petit_card_segment` invoqué à la VARIABLE Tpb (bo GENUINE), {Tpb⊂a,Tpb≠∅}
    déchargés en implication, généralisé sur Tpb (absent du bo), instancié au TERME PB.
    bo_pp = la forme GENUINE de est_bien_ordonne(Ro,a) que plus_petit dépose à T=variable."""
    va = _t(a)
    PB = HTP.pullback(a, Ro, S)
    vT = var(_TPB)
    pp = BOIO.plus_petit_card_segment(Ro, a, _TPB, m, xs)         # [bo, Tpb⊂a, Tpb≠∅]
    Tsub = inclus(vT, va)
    Tne = non(egal(vT, E.VIDE))
    bo = [h for h in pp.hypotheses if h not in {Tsub, Tne}]
    assert len(bo) == 1, f"extraction bo de plus_petit ambiguë: {len(bo)}"
    bo_f = bo[0]
    # décharger Tne (interne), Tsub → implication ( Tsub ⇒ ( Tne ⇒ concl ) ) ; mais on veut
    # ( Tsub et Tne ) ⇒ concl pour matcher l'appel.  On décharge en conjonction.
    HsT = N.assume(et(Tsub, Tne))
    pp1 = N.modus_ponens(conjonction_elim_gauche(HsT), N.loi_deduction(Tsub, pp))
    pp2 = N.modus_ponens(conjonction_elim_droite(HsT), N.loi_deduction(Tne, pp1))   # concl [bo, (Tsub∧Tne)]
    imp = N.loi_deduction(et(Tsub, Tne), pp2)                    # (Tsub∧Tne) ⇒ concl  [bo]
    g = N.generalisation(_TPB, imp)                              # (∀Tpb)(...)  [bo]  (Tpb ∉ bo)
    inst = instancie(g, PB)                                      # (PB⊂a ∧ PB≠∅) ⇒ (∃m)…  [bo]
    return inst


def _bo_form_pp(Ro="Ro", a="a", m="ms", xs="xs"):
    """La FORME GENUINE de bo(Ro,a) portée par _plus_petit_PB (= celle de plus_petit à
    T=variable Tpb)."""
    va = _t(a)
    vT = var(_TPB)
    pp = BOIO.plus_petit_card_segment(Ro, a, _TPB, m, xs)
    bo = [h for h in pp.hypotheses if h not in {inclus(vT, va), non(egal(vT, E.VIDE))}]
    assert len(bo) == 1
    return bo[0]


# ════════════════════════════════════════════════════════════════════════════
#  3️⃣  CLAUSE MIN CLEAN — le ≤-min de S (cas S'≠∅), top borné par µ≤Card a.
# ════════════════════════════════════════════════════════════════════════════
def clause_min_clean(Ro="Ro", a="a", S="S", m="ms", xs="xs", c="x", w=_LIT_T):
    """⊢ { bo_canon(Ro,a),  S⊂[0,a],  realisation_segment_garde_clean(Ro,a),
           (∃cgate)(cgate∈S et ¬Eq(cgate,Card a)) }
            ⊢ (∃m)( m∈S et (∀c)( c∈S ⇒ R_induit{m,c} ) ).   [binders m='m', c='x']

    🎯 RE-PREUVE de la clause-min RESTREINTE à S∖{top}, alimentée par l'onto CLEAN.
    Le pullback PB=pullback(a,Ro,S) est NON vide (pullback_non_vide_clean, condition de
    branche) ; `plus_petit_card_segment` (CLOS) en extrait m avec µ:=Card(seg m) ≤-minorant
    de {Card(seg w)|w∈PB}.  µ∈S (pullback_into, CLOS).  Pour c∈S, CASE-SPLIT sur Eq(c,Card a) :
      • ¬Eq(c,Card a) : l'onto CLEAN réalise c=Card(seg w), w∈PB ⇒ µ≤Card(seg w)=c ;
      • Eq(c,Card a)  : c=Card a ; µ∈S⊂[0,a] ⇒ µ≤a ⇒ Card µ≤Card a, et est_cardinal(µ)
        ⇒ Card µ=µ ⇒ µ≤Card a=c (le TOP est le ≤-MAX).
    Dans les deux cas µ≤c, donc R_induit{µ,c}.  binders DISTINCTS : m='ms' (min-élément),
    xs='xs' (min-∀ de plus_petit), c='x' (∀ de la clause), w='tw' (témoin onto/réalisation).
    theorie=22."""
    va, vS = _t(a), _t(S)
    mn = m if isinstance(m, str) else m.nom
    xsn = xs if isinstance(xs, str) else xs.nom
    cn = c if isinstance(c, str) else c.nom
    wn = w if isinstance(w, str) else w.nom
    vm, vxs, vc, vw = var(mn), var(xsn), var(cn), var(wn)
    interv = intervalle_0a(a)
    Rind = ordre_induit_intervalle(a)
    carda = cardinal(va)
    PB = HTP.pullback(a, Ro, S)
    mu = lambda tm: cardinal(seg(Ro, a, tm))

    # ── PB ⊆ a (CLOS), PB ≠ ∅ (condition de branche) → ≤-min m de PB.
    #   ⚠️ plus_petit_card_segment au TERME PB porterait un bo DÉGÉNÉRÉ (PB-liant-terme dans
    #   le slot ∀X) ⇒ NON déchargeable.  On l'invoque à la VARIABLE « Tpb », on décharge
    #   {Tpb⊂a, Tpb≠∅} en implication, on GÉNÉRALISE sur Tpb (absent du bo, qui ne porte
    #   que `a`) puis on INSTANCIE au TERME PB — le bo reste GENUINE (binders propres).
    pb_sub = HTP.pullback_inclus_a(a, Ro, S)                       # PB ⊂ a   [CLOS]
    pb_ne = pullback_non_vide_clean(a, Ro, S, _CFRESH, wn)         # PB ≠ ∅   [S⊂[0,a], realC, S_top]
    pp = _plus_petit_PB(Ro, a, S, mn, xsn)                        # [bo_pp] ⊢ (PB⊂a ∧ PB≠∅) ⇒ (∃ms)…
    pp = N.modus_ponens(conjonction_intro(pb_sub, pb_ne), pp)     # (∃ms)…  [bo_pp, S⊂[0,a], realC, S_top]

    # ── per-témoin m : corps_min = m∈PB et (∀xs)(xs∈PB ⇒ Card(seg m)≤Card(seg xs))
    corps_min = et(appartient(vm, PB),
        pourtout(xsn, impl(appartient(vxs, PB), inf_egal_card(mu(vm), mu(vxs)))))
    Hwit = N.assume(corps_min)
    m_in_PB = conjonction_elim_gauche(Hwit)                       # m∈PB
    min_le = conjonction_elim_droite(Hwit)                        # (∀xs∈PB) Card(seg m)≤Card(seg xs)
    vmu = mu(vm)                                                  # µ := Card(seg m)

    # ── µ∈S via pullback_into (CLOS) : (∀t)(t∈PB ⇒ Card(seg t)∈S), instancié à m
    into = HTP.pullback_into(a, Ro, S, BOIO._BT)                  # (∀t)(t∈PB ⇒ Card(seg t)∈S)  CLOS
    mu_in_S = N.modus_ponens(m_in_PB, instancie(into, vm))        # µ∈S
    mu_in_interv = N.modus_ponens(mu_in_S, HTP._inclus_S_interv(a, S, vmu))  # µ∈[0,a]
    mu_le_a = HTP._c_le_a(a, vmu, mu_in_interv)                   # µ ≤ a
    est_card_mu = N.modus_ponens(mu_in_interv, _est_cardinal_de_interv(a, vmu))  # est_cardinal(µ)

    # ── per-c : c∈S ⊢ R_induit{µ,c}   (CASE-SPLIT sur Eq(c,Card a))
    Hc = N.assume(appartient(vc, vS))                            # c∈S
    c_in_interv = N.modus_ponens(Hc, HTP._inclus_S_interv(a, S, vc))   # c∈[0,a]

    #   onto CLEAN : (c∈S et ¬Eq(c,Card a)) ⇒ (∃w)(w∈PB et c=Card(seg w))  [witness w='tw']
    onto = pullback_onto_clean(a, Ro, S, _CFRESH, wn)
    onto_c = instancie(onto, vc)

    #   BRANCHE A : ¬Eq(c,Card a) ⇒ µ≤c
    H_neq = N.assume(non(equipotent(vc, carda)))                 # ¬Eq(c,Card a)
    cond = conjonction_intro(Hc, H_neq)
    ex_w = N.modus_ponens(cond, onto_c)                         # (∃w)(w∈PB et c=Card(seg w))
    corps_w = et(appartient(vw, PB), egal(vc, mu(vw)))
    Hw = N.assume(corps_w)
    w_in_PB = conjonction_elim_gauche(Hw)
    c_eq = conjonction_elim_droite(Hw)                          # c = Card(seg w)
    mu_le_segw = N.modus_ponens(w_in_PB, instancie(min_le, vw))  # µ ≤ Card(seg w)
    c_eq_sym = HTP._sym(vc, mu(vw), c_eq)                       # Card(seg w) = c
    mu_le_c_A = BOIO._leib_rhs_le(vmu, mu(vw), vc, mu_le_segw, c_eq_sym)  # µ ≤ c
    body_w = N.loi_deduction(corps_w, mu_le_c_A)
    mu_le_c_fromA = N.modus_ponens(ex_w, existe_elimination(body_w, wn))  # µ≤c  [¬Eq, c∈S, …]
    brA = N.loi_deduction(non(equipotent(vc, carda)), mu_le_c_fromA)      # ¬Eq(c,Card a) ⇒ µ≤c

    #   BRANCHE B : Eq(c,Card a) ⇒ µ≤c  (c=Card a, µ≤Card a via transport)
    H_eq = N.assume(equipotent(vc, carda))                      # Eq(c, Card a)
    #   c = Card a :  Card c = Card(Card a) = Card a, et est_cardinal(c) ⇒ Card c = c ⇒ c=Card a
    cardc_eq_cardcarda = N.modus_ponens(H_eq, _card_eq_si_eq(vc, carda))  # Card c = Card(Card a)
    cardcarda_eq_carda = _cardinal_idempotent_t(va)             # Card(Card a) = Card a
    cardc_eq_carda = composer_egalites(cardc_eq_cardcarda, cardcarda_eq_carda)  # Card c = Card a
    est_card_c = N.modus_ponens(c_in_interv, _est_cardinal_de_interv(a, vc))    # est_cardinal(c)
    cc_eq_c = N.modus_ponens(est_card_c, _cardinal_est_son_cardinal(vc))        # Card c = c
    c_eq_cardc = N.modus_ponens(cc_eq_c, _sym_eq(cardinal(vc), vc))             # c = Card c
    c_eq_carda = composer_egalites(c_eq_cardc, cardc_eq_carda)                  # c = Card a
    #   µ ≤ Card a :  µ≤a ⇒ Card µ≤Card a (transport), Card µ=µ ⇒ µ≤Card a
    cardmu_le_carda = N.modus_ponens(mu_le_a, _transporte_card(vmu, va))        # Card µ ≤ Card a
    cmu_eq_mu = N.modus_ponens(est_card_mu, _cardinal_est_son_cardinal(vmu))    # Card µ = µ
    #   rewrite Card µ → µ on the LHS of (Card µ ≤ Card a) :
    mu_le_carda = HTP._leib_transport(cardinal(vmu), vmu, cmu_eq_mu,
                                      lambda w: inf_egal_card(w, carda), cardmu_le_carda)  # µ ≤ Card a
    #   µ ≤ c  via c = Card a (rewrite Card a → c on RHS of µ≤Card a)
    carda_eq_c = N.modus_ponens(c_eq_carda, _sym_eq(vc, carda))                 # Card a = c
    mu_le_c_B = HTP._leib_transport(carda, vc, carda_eq_c,
                                    lambda w: inf_egal_card(vmu, w), mu_le_carda)  # µ ≤ c
    brB = N.loi_deduction(equipotent(vc, carda), mu_le_c_B)      # Eq(c,Card a) ⇒ µ≤c

    #   CASE-SPLIT : tiers_exclu Eq(c,Card a) ∨ ¬Eq(c,Card a)
    te = tiers_exclu(equipotent(vc, carda))
    mu_le_c = cas(te, brB, brA)                                 # µ ≤ c   [c∈S, …]

    # ── R_induit{µ,c} = ((µ≤c et µ∈[0,a]) et c∈[0,a])
    Rind_mu_c = conjonction_intro(conjonction_intro(mu_le_c, mu_in_interv), c_in_interv)
    assert Rind_mu_c.conclusion == Rind(vmu, vc), "R_induit{µ,c} mal formé"
    body_c = N.loi_deduction(appartient(vc, vS), Rind_mu_c)     # c∈S ⇒ R_induit{µ,c}
    body_all_c = N.generalisation(cn, body_c)                  # (∀c)(c∈S ⇒ R_induit{µ,c})
    corps_mu = conjonction_intro(mu_in_S, body_all_c)          # µ∈S et (∀c∈S)R_induit

    # ── introduire (∃µ) [binder « m » de clause_plus_petit] avec témoin µ
    bm = "m"
    vbm = var(bm)
    body_r = et(appartient(vbm, vS),
        pourtout(cn, impl(appartient(vc, vS), Rind(vbm, vc))))
    but = existe(bm, body_r)
    ex_mu = N.modus_ponens(corps_mu, N.s5(body_r, vmu, bm))
    wit_imp = N.loi_deduction(corps_min, ex_mu)
    ex_imp = existe_elimination(wit_imp, mn)
    res = N.modus_ponens(pp, ex_imp)
    assert res.conclusion == _clause_corps_S(a, S), "clause_min_clean ≠ corps clause-S"
    return res


def _clause_corps_S(a="a", S="S", m="m", c="x"):
    """Le CORPS de la clause pour S :  (∃m)( m∈S et (∀c)( c∈S ⇒ R_induit{m,c} ) )
    [binders m='m', c='x' — ceux de bon_ordre_intervalle]."""
    vS = _t(S)
    vm, vc = var(m), var(c)
    Rind = ordre_induit_intervalle(a)
    return existe(m, et(appartient(vm, vS),
        pourtout(c, impl(appartient(vc, vS), Rind(vm, vc)))))


# ════════════════════════════════════════════════════════════════════════════
#  CAS B — S = {Card a}  ( ¬S_top ) : min(S) = Card a  par RÉFLEXIVITÉ.
# ════════════════════════════════════════════════════════════════════════════
def clause_min_top_only(Ro="Ro", a="a", S="S", c0="c0", c="x", topb=_CFRESH):
    """⊢ { S⊂[0,a],  S≠∅,  ¬(∃cgate)(cgate∈S et ¬Eq(cgate,Card a)) }
            ⊢ (∃m)( m∈S et (∀c)( c∈S ⇒ R_induit{m,c} ) ).

    🎯 CAS où S n'a AUCUN élément ≠ Card a : tout c∈S vérifie Eq(c,Card a), donc (c∈[0,a]
    cardinal) c=Card a ; S est le SINGLETON {Card a}.  Un témoin c0∈S (S≠∅) est le min :
    pour tout x∈S, x=Card a=c0, donc c0≤x se réduit à la RÉFLEXIVITÉ c0≤c0.  Le TOP, étant
    le ≤-MAX, EST son propre (et l'unique) min ici.  Le liant de ¬S_top est `topb`='cgate'
    (= celui de _S_top, pour matcher le case-split de clause_pour_S_clean).  theorie=22,
    PROUVÉ (réflexivité), JAMAIS postulé."""
    from bourbaki.ensembles.base.ensembles_vide import non_vide_ssi_element
    from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
    va, vS = _t(a), _t(S)
    c0n = c0 if isinstance(c0, str) else c0.nom
    cn = c if isinstance(c, str) else c.nom
    tbn = topb if isinstance(topb, str) else topb.nom
    vc0, vc = var(c0n), var(cn)
    carda = cardinal(va)
    Rind = ordre_induit_intervalle(a)

    # ── ¬S_top (liant cgate=topb, pour matcher le case-split)
    notSt = N.assume(non(_S_top(a, S, tbn)))                      # ¬(∃cgate)(cgate∈S et ¬Eq(cgate,Card a))

    def _eq_carda_de(vz, Hz_in_S):
        """De z∈S et ¬S_top déduit Eq(z,Card a)."""
        #  z∈S ∧ ¬Eq(z,Card a) ⇒ (∃cgate)(...)  (s5) ; contredit ¬S_top ⇒ Eq (consequentia).
        Hnq = N.assume(non(equipotent(vz, carda)))               # ¬Eq(z,Card a)
        corps = conjonction_intro(Hz_in_S, Hnq)                  # z∈S et ¬Eq(z,Card a)
        body_st = et(appartient(var(tbn), vS), non(equipotent(var(tbn), carda)))
        ex_st = N.modus_ponens(corps, N.s5(body_st, vz, tbn))    # (∃cgate)(...)  = _S_top
        falso = HTP._ex_falso(ex_st, notSt, equipotent(vz, carda))   # Eq(z,Card a) [z∈S,¬Eq,¬St]
        imp_nq = N.loi_deduction(non(equipotent(vz, carda)), falso)  # ¬Eq ⇒ Eq(z,Card a)
        #  (¬Eq ⇒ Eq) ⊢ Eq  via tiers exclu + cas (consequentia mirabilis)
        P = equipotent(vz, carda)
        te = tiers_exclu(P)                                          # P ∨ ¬P
        return cas(te, a_implique_a(P), imp_nq)                      # Eq(z,Card a)

    # ── témoin c0 ∈ S (de S≠∅)
    nv = non_vide_ssi_element(vS)
    H_ne = N.assume(non(egal(vS, E.VIDE)))
    ex_z = N.modus_ponens(H_ne, equivalence_avant(nv))           # (∃z) z∈S
    ex_c0 = N.modus_ponens(ex_z, equivalence_avant(
        alpha_existe("z", c0n, appartient(var("z"), vS))))       # (∃c0) c0∈S

    # ── per-c0 : c0∈S ⊢ corps clause (témoin m=c0)
    Hc0 = N.assume(appartient(vc0, vS))                          # c0∈S
    c0_interv = N.modus_ponens(Hc0, HTP._inclus_S_interv(a, S, vc0))  # c0∈[0,a]
    eq_c0 = _eq_carda_de(vc0, Hc0)                               # Eq(c0,Card a)
    c0_eq_carda = _c_eq_carda(a, vc0, c0_interv, eq_c0)          # c0 = Card a

    # ── (∀c)(c∈S ⇒ R_induit{c0,c}) :  pour c∈S, c=Card a=c0 ⇒ c0≤c (réflexivité)
    Hc = N.assume(appartient(vc, vS))                            # c∈S
    c_interv = N.modus_ponens(Hc, HTP._inclus_S_interv(a, S, vc))   # c∈[0,a]
    eq_c = _eq_carda_de(vc, Hc)                                  # Eq(c,Card a)
    c_eq_carda = _c_eq_carda(a, vc, c_interv, eq_c)              # c = Card a
    #   c0 = c :  c0 = Card a = c
    carda_eq_c = N.modus_ponens(c_eq_carda, _sym_eq(vc, carda))  # Card a = c
    c0_eq_c = composer_egalites(c0_eq_carda, carda_eq_c)         # c0 = c
    #   c0 ≤ c : de c0≤c0 (réflexivité) réécrit c0→c sur le RHS
    c0_le_c0 = instancie(N.generalisation("Xrf", inf_egal_reflexif("Xrf")), vc0)  # c0 ≤ c0
    c0_le_c = HTP._leib_transport(vc0, vc, c0_eq_c,
                                  lambda ww: inf_egal_card(vc0, ww), c0_le_c0)   # c0 ≤ c
    Rind_c0_c = conjonction_intro(conjonction_intro(c0_le_c, c0_interv), c_interv)
    assert Rind_c0_c.conclusion == Rind(vc0, vc), "R_induit{c0,c} mal formé"
    body_c = N.loi_deduction(appartient(vc, vS), Rind_c0_c)
    body_all_c = N.generalisation(cn, body_c)                   # (∀c)(c∈S ⇒ R_induit{c0,c})
    corps_c0 = conjonction_intro(Hc0, body_all_c)               # c0∈S et (∀c∈S)R_induit{c0,c}

    # ── introduire (∃m) [binder « m »] avec témoin c0
    bm = "m"
    vbm = var(bm)
    body_r = et(appartient(vbm, vS), pourtout(cn, impl(appartient(vc, vS), Rind(vbm, vc))))
    ex_m = N.modus_ponens(corps_c0, N.s5(body_r, vc0, bm))      # (∃m)(...)  [c0∈S, ¬St]
    from_c0 = N.modus_ponens(ex_c0, existe_elimination(N.loi_deduction(appartient(vc0, vS), ex_m), c0n))
    assert from_c0.conclusion == _clause_corps_S(a, S), "clause_min_top_only ≠ corps clause-S"
    return from_c0


def _c_eq_carda(a, vz, h_z_interv, h_eq):
    """De z∈[0,a] [h_z_interv] et Eq(z,Card a) [h_eq] déduit ⊢ z = Card a.
    (z cardinal ⇒ Card z = z ; Eq ⇒ Card z = Card(Card a) = Card a ⇒ z = Card a.)"""
    va = _t(a)
    carda = cardinal(va)
    est_card_z = N.modus_ponens(h_z_interv, _est_cardinal_de_interv(a, vz))   # est_cardinal(z)
    cz_eq_z = N.modus_ponens(est_card_z, _cardinal_est_son_cardinal(vz))      # Card z = z
    z_eq_cz = N.modus_ponens(cz_eq_z, _sym_eq(cardinal(vz), vz))             # z = Card z
    cz_eq_ccarda = N.modus_ponens(h_eq, _card_eq_si_eq(vz, carda))           # Card z = Card(Card a)
    ccarda_eq_carda = _cardinal_idempotent_t(va)                            # Card(Card a) = Card a
    cz_eq_carda = composer_egalites(cz_eq_ccarda, ccarda_eq_carda)          # Card z = Card a
    return composer_egalites(z_eq_cz, cz_eq_carda)                          # z = Card a


# ════════════════════════════════════════════════════════════════════════════
#  4️⃣  CLAUSE pour S — CASE-SPLIT sur S_top  (S a un élément ≠ Card a, ou non).
# ════════════════════════════════════════════════════════════════════════════
def clause_pour_S_clean(Ro="Ro", a="a", S="S"):
    """⊢ { bo_pp(Ro,a),  realisation_segment_garde_clean(Ro,a),  S⊂[0,a],  S≠∅ }
            ⊢ (∃m)( m∈S et (∀c)( c∈S ⇒ R_induit{m,c} ) ).

    🎯 LE CASE-SPLIT (tiers_exclu sur S_top = (∃c)(c∈S et ¬Eq(c,Card a))) :
      • S_top : `clause_min_clean` (≤-min de S via pullback restreint, top borné par µ≤Card a) ;
      • ¬S_top : `clause_min_top_only` (S={Card a}, min = Card a par réflexivité).
    Les deux branches CONCLUENT le MÊME corps de clause _clause_corps_S.  theorie=22."""
    va, vS = _t(a), _t(S)
    cible = _clause_corps_S(a, S)
    St = _S_top(a, S, _CFRESH)

    # BRANCHE S_top : clause_min_clean (consomme bo_pp, realC, S⊂[0,a], S_top)
    cmc = clause_min_clean(Ro, a, S)                             # [bo_pp, S⊂[0,a], realC, S_top]
    brA = N.loi_deduction(St, cmc)                              # S_top ⇒ corps  [bo_pp, S⊂[0,a], realC]

    # BRANCHE ¬S_top : clause_min_top_only (consomme S⊂[0,a], S≠∅, ¬S_top)
    cto = clause_min_top_only(Ro, a, S)                         # [S⊂[0,a], S≠∅, ¬S_top]
    brB = N.loi_deduction(non(St), cto)                        # ¬S_top ⇒ corps  [S⊂[0,a], S≠∅]

    te = tiers_exclu(St)                                       # S_top ∨ ¬S_top
    res = cas(te, brA, brB)                                    # corps  [bo_pp, realC, S⊂[0,a], S≠∅]
    assert res.conclusion == cible, "clause_pour_S_clean ≠ corps clause-S"
    return res


def clause_plus_petit_clean(Ro="Ro", a="a", S="S"):
    """⊢ { bo_pp(Ro,a),  realisation_segment_garde_clean(Ro,a) }
            ⊢ clause_plus_petit( ≤_induit , [0,a] )   [binders X=S, b=m, w=x].

    🎯 Décharge ( S⊂[0,a] et S≠∅ ) sur la clause pour S (clause_pour_S_clean), généralise
    sur S.  theorie=22."""
    va, vS = _t(a), _t(S)
    interv = intervalle_0a(a)
    Ssub = inclus(vS, interv)
    Sne = non(egal(vS, E.VIDE))
    HsS = et(Ssub, Sne)
    cs = clause_pour_S_clean(Ro, a, S)                         # [bo_pp, realC, S⊂[0,a], S≠∅]
    HHsS = N.assume(HsS)
    cs2 = N.modus_ponens(conjonction_elim_gauche(HHsS), N.loi_deduction(Ssub, cs))
    cs2 = N.modus_ponens(conjonction_elim_droite(HHsS), N.loi_deduction(Sne, cs2))
    imp_body = N.loi_deduction(HsS, cs2)                       # HsS ⇒ corps  [bo_pp, realC]
    return N.generalisation(S, imp_body)                       # clause_plus_petit  [bo_pp, realC]


# ════════════════════════════════════════════════════════════════════════════
#  5️⃣  LE GATE — bon_ordre_intervalle(a) / cardinaux_bien_ordonnes(a) CLOS.
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_intervalle_sous_bo(Ro="Ro", a="a", S="S"):
    """⊢ { bo_pp(Ro,a),  realisation_segment_garde_clean(Ro,a) }  ⊢  bon_ordre_intervalle(a).

    🎯 Conjoint la PARTIE ORDRE (relation_ordre_dans_intervalle, CLOSE) et la CLAUSE
    (clause_plus_petit_clean).  Conclusion == bon_ordre_intervalle(a) LITTÉRAL.  theorie=22."""
    clause = clause_plus_petit_clean(Ro, a, S)                 # [bo_pp, realC]
    rod = relation_ordre_dans_intervalle(a)                    # CLOS
    res = conjonction_intro(rod, clause)
    assert res.conclusion == bon_ordre_intervalle(a), \
        "conclusion ≠ bon_ordre_intervalle(a)"
    return res


# ensemble INTERNE ≠ 'a' : évite la collision du liant min-élément 'a' de est_bien_ordonne
# avec le nom d'ensemble (sinon `instancie` canonicalise le liant en '@0' ≠ forme bâtie).
_AINT = "agate"


def _bon_ordre_intervalle_close_raw(a, Ro="Ro", S="S"):
    """⊢ bon_ordre_intervalle(a)  CLOS, pour un nom d'ensemble `a` ≠ liant min-élément 'a'."""
    boi = bon_ordre_intervalle_sous_bo(Ro, a, S)               # [bo_pp, realC]
    bo_pp = _bo_form_pp(Ro, a)
    realC = realisation_segment_garde_clean(Ro, a)
    bo_clean = _bo_form_clean(Ro, a)

    # (1) UNIFIER : convertir l'hyp bo_pp en bo_clean (α-équivalence) ⇒ une SEULE forme bo.
    eq_cp = _equiv_clean_pp(Ro, a)                             # bo_clean ⇔ bo_pp   CLOS
    bo_pp_from_clean = N.modus_ponens(N.assume(bo_clean), equivalence_avant(eq_cp))  # [bo_clean] ⊢ bo_pp
    boi_cl = N.modus_ponens(bo_pp_from_clean, N.loi_deduction(bo_pp, boi))  # [bo_clean, realC] ⊢ boi

    # (2) décharger realisation_segment_garde_clean via realisation_garde_clean ([bo_clean])
    rgc = realisation_garde_clean(Ro, a)                       # [bo_clean] ⊢ realC
    boi1 = N.modus_ponens(rgc, N.loi_deduction(realC, boi_cl)) # [bo_clean] ⊢ boi   (UNE seule hyp bo)

    # (3) éliminer bo_clean via Zermelo  (∃Ro) bo_clean  (Ro libre UNIQUEMENT dans bo_clean)
    imp_cl = N.loi_deduction(bo_clean, boi1)                   # bo_clean ⇒ boi   CLOS
    ex_cl_imp = existe_elimination(imp_cl, Ro)                 # (∃Ro)bo_clean ⇒ boi
    zerm_cl = _zermelo_bo_clean(a, Ro)                         # (∃Ro) bo_clean   CLOS
    res = N.modus_ponens(zerm_cl, ex_cl_imp)                   # bon_ordre_intervalle(a)
    assert res.conclusion == bon_ordre_intervalle(a), \
        "conclusion ≠ bon_ordre_intervalle(a)"
    assert res.est_clos, "bon_ordre_intervalle_close_raw NON clos"
    return res


def bon_ordre_intervalle_close(a="a", Ro="Ro", S="S"):
    """⊢  bon_ordre_intervalle(a)   (== est_bien_ordonne(≤_induit,[0,a]), LITTÉRAL).  CLOS, 0 hyp.

    🎯🎯 LE GATE ℕ #1 INCONDITIONNEL.  Construit pour l'ensemble INTERNE `agate` (≠ liant
    min-élément 'a' de est_bien_ordonne ⇒ pas de canonicalisation de liant lors de
    l'instanciation Zermelo), puis TRANSPORTÉ au nom `a` demandé (généralisation +
    instanciation — les liants de la cible (m,x,S…) ≠ a/agate, aucune capture).

    Sous { bo(Ro,a), realisation_segment_garde_clean } : on UNIFIE les deux formes de bon
    ordre (bo_pp de plus_petit, bo_clean de realisation) par α-équivalence en UNE, déchargée
    par ZERMELO (_zermelo_bo, CLOS).  HYPOTHÈSE SURVIVANTE : AUCUNE.  theorie=22."""
    raw = _bon_ordre_intervalle_close_raw(_AINT, Ro, S)        # ⊢ bon_ordre_intervalle(agate)  CLOS
    an = a if isinstance(a, str) else a.nom
    res = instancie(N.generalisation(_AINT, raw), _t(a))       # ⊢ bon_ordre_intervalle(a)
    assert res.conclusion == bon_ordre_intervalle(a), \
        "conclusion ≠ bon_ordre_intervalle(a) [après transport]"
    assert res.est_clos, "bon_ordre_intervalle_close NON clos"
    return res


def cardinaux_bien_ordonnes_close(a="a", Ro="Ro", S="S"):
    """⊢  cardinaux_bien_ordonnes(a)   (LITTÉRAL).  CLOS, 0 hypothèse.

    🎯🎯 Feed `bon_ordre_intervalle_close` (CLOS) dans `cardinaux_bien_ordonnes_de_bon_ordre`
    (réduction CLOSE).  theorie=22, conclusion == cardinaux_bien_ordonnes(a)."""
    gd = bon_ordre_intervalle_close(a, Ro, S)                  # CLOS ⊢ bon_ordre_intervalle(a)
    cbo = cardinaux_bien_ordonnes_de_bon_ordre(a)             # [bon_ordre_intervalle] ⊢ cbo
    res = N.modus_ponens(gd, N.loi_deduction(bon_ordre_intervalle(a), cbo))
    assert res.conclusion == cardinaux_bien_ordonnes(a), \
        "conclusion ≠ cardinaux_bien_ordonnes(a)"
    assert res.est_clos, "cardinaux_bien_ordonnes_close NON clos"
    return res


def _bo_min_binders(bo_form):
    """Extrait (setb, elemb, compb) — les 3 liants de la clause-minimum d'un
    est_bien_ordonne (2ᵉ conjoint).  Encodages : et(A,B)=non(ou(¬A,¬B)),
    impl(A,B)=ou(¬A,B), pourtout(z,R)=non(exists(z,¬R))."""
    ou_top = bo_form.sous[0]                      # ou(¬ordre, ¬minclause)
    minclause = ou_top.sous[1].sous[0]            # ¬minclause → minclause = (∀setb)(...)
    ex_set = minclause.sous[0]                    # exists(setb, ¬impl)
    setb = ex_set.lieur
    impl_f = ex_set.sous[0].sous[0]               # impl(CS, ex_elem) = ou(¬CS, ex_elem)
    ex_elem = impl_f.sous[1]                       # exists(elemb, body)
    elemb = ex_elem.lieur
    body_ou = ex_elem.sous[0].sous[0]             # ou(¬(elem∈set), ¬pourtout)
    forall_comp = body_ou.sous[1].sous[0]         # pourtout(compb,...) = non(exists(compb,¬R))
    compb = forall_comp.sous[0].lieur
    return setb, elemb, compb


# ── cibles (tests miroir) ─────────────────────────────────────────────────────
def bon_ordre_intervalle_close_cible(a="a"):
    """ÉNONCÉ-cible : bon_ordre_intervalle(a)  (== la cible déposée)."""
    return bon_ordre_intervalle(a)


def cardinaux_bien_ordonnes_close_cible(a="a"):
    """ÉNONCÉ-cible : cardinaux_bien_ordonnes(a)  (== la cible déposée)."""
    return cardinaux_bien_ordonnes(a)


__all__ = [
    "realisation_segment_garde_clean", "realisation_garde_clean",
    "pullback_onto_clean", "pullback_onto_clean_cible",
    "pullback_non_vide_clean",
    "clause_min_clean", "clause_min_top_only", "clause_pour_S_clean",
    "clause_plus_petit_clean",
    "bon_ordre_intervalle_sous_bo",
    "bon_ordre_intervalle_close", "cardinaux_bien_ordonnes_close",
    "bon_ordre_intervalle_close_cible", "cardinaux_bien_ordonnes_close_cible",
]
