"""§III.4 — FERMETURE du GATE ℕ : `bon_ordre_intervalle(a)` réduit au SEUL maillon
RÉALISATION (`realisation_segment`), en CONTOURNANT le défaut de liant-TERME de
`hyp_transport_ordinal` / `bo_form_artefact`.

────────────────────────────────────────────────────────────────────────────────
LE DÉFAUT STRUCTUREL CONTOURNÉ (rapporté, confirmé empiriquement).

`bon_ordre_intervalle_ordinal(a)` (ensembles_bon_ordre_intervalle_ordinal) prouve
`bon_ordre_intervalle(a)` sous l'UNIQUE hypothèse `hyp_transport_ordinal(a)`, mais
cette dernière contient un CONJOINT DÉGÉNÉRÉ `bo_form_artefact(a,Ro,S)` :
`_bo_form_canon(a,Ro,pullback(a,Ro,S),_BM,_BX)` passe le TERME COMPOSÉ
`pullback(a,Ro,S)` dans le SLOT du LIANT « X » (∀X) de `est_bien_ordonne`.  AUCUNE
règle du noyau (generalisation / s5 / alpha_existe ne lient QUE des NOMS de variable)
ne peut PRODUIRE ni α-renommer un liant-terme — vérifié : la formule porte un `.lieur`
de type `Terme` (tag `app`) là où tout liant bien formé est une chaîne.  Ce conjoint
est donc STRUCTURELLEMENT NON DÉRIVABLE ; `hyp_transport_ordinal(a)` est NON close.

LE CONTOURNEMENT (ce module).  Le défaut vient UNIQUEMENT de ce que le pullback
entre dans le slot ∀X comme TERME.  Or `clause_min_intervalle_de_pullback(Ro,a,S,T,…)`
prend `T` en PARAMÈTRE : appelé avec `T` = une VARIABLE FRAÎCHE `« Tpb »` (chaîne),
il dépose un `est_bien_ordonne(_R_de(Ro),a)` BIEN FORMÉ (liant ∀Tpb = chaîne) et 5
hypothèses bien formées { into(Tpb), onto(Tpb), Tpb⊂a, Tpb≠∅, S⊂[0,a] }.  Sa
CONCLUSION — le ≤-min de S — NE MENTIONNE PAS Tpb.  On peut donc :

  (1) décharger les 4 propriétés { Tpb⊂a, Tpb≠∅, into, onto } via un corps B(Tpb),
  (2) ÉLIMINER ∃Tpb (Tpb non libre dans la conclusion ni dans le reste) ;
      le témoin de (∃Tpb)B(Tpb) est le TERME pullback `PB`, fourni par
      `hyp_transport_corps_preuve` (CLOS modulo {S⊂[0,a], S≠∅, realisation}) ;
  (3) décharger (S⊂[0,a] et S≠∅), généraliser sur S → clause_plus_petit(≤_induit,[0,a]) ;
  (4) conjoindre la PARTIE ORDRE (relation_ordre_dans_intervalle, CLOSE) →
      est_bien_ordonne(≤_induit,[0,a]) = bon_ordre_intervalle(a) sous { bo_form(Ro),
      realisation } ;
  (5) ÉLIMINER ∃Ro : `bo_form(Ro)` = est_bien_ordonne(_R_de(Ro),a) BIEN FORMÉ est
      DÉCHARGÉ par ZERMELO ((∃R) est_bien_ordonne(_R_de(R),a), CLOS) α-renommé vers
      les binders de `bo_form` ; `realisation` est Ro-INDÉPENDANTE (seg(a,·,t) ne
      porte pas Ro).

RÉSULTAT — `bon_ordre_intervalle_depuis_realisation(a)` :

    ⊢ { (∀c) realisation_segment(Ro,a,c) }  ⊢  bon_ordre_intervalle(a)
                                                 (== la cible LITTÉRALEMENT).

soit le GATE ℕ réduit AU SEUL MAILLON HONNÊTE — la RÉALISATION ordinal↔cardinal :
« tout cardinal c≤a est le cardinal d'un segment initial seg(a,Ro,t) de (a,Ro) ».
PLUS de liant-TERME, PLUS de `hyp_transport_ordinal`.  Et si `realisation_segment`
est CLOS, alors `bon_ordre_intervalle(a)` et `cardinaux_bien_ordonnes(a)` le sont.

INVARIANT : theorie_ensembles() = 22.  Rien postulé : tout DÉRIVE des théorèmes CLOS
du dépôt (clause_min, hyp_transport_corps_preuve, Zermelo, relation_ordre_dans_intervalle)
plus l'unique hypothèse `realisation_segment`, isolée, JAMAIS postulée.  NE MODIFIE
AUCUN fichier existant.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.ensembles.ensembles_abrege import est_relation_ordre_dans
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_transitivite, et_congruence_droite,
    ou_congruence, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, alpha_pour_tout,
    congruence_pour_tout, congruence_existe,
)

import bourbaki.cardinaux.ensembles_bon_ordre_intervalle_ordinal as BOIO
import bourbaki.cardinaux.ensembles_hyp_transport_ordinal_preuve as HTP
import bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zermelo as Z
from bourbaki.cardinaux.ensembles_segments_construction import _R_de
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.cardinaux.ensembles_segments_construction import seg
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    intervalle_0a, bon_ordre_intervalle,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal_ordre import (
    relation_ordre_dans_intervalle,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _dech(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (loi_deduction puis modus_ponens)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ── binders canoniques du contournement (alignés clause_min / corps / Zermelo) ──
#   Tpb : la VARIABLE FRAÎCHE qui remplace le terme pullback dans le slot ∀X.
#   ms/xw : binders du ⊂-min de plus_petit_card_segment (m='ms', x='xw').
#   _BC='x', _BX='xw', _BT='tt' : binders de hyp_realisation_onto / _min (cf. BOIO).
_TPB = "Tpb"
_BM, _BX, _BT, _BC = "ms", "xw", BOIO._BT, BOIO._BC   # ms, xw, tt, x


def realisation_segment(Ro="Ro", a="a", c="x", t="xw"):
    """ÉNONCÉ (le SEUL maillon honnête) — « tout cardinal c≤a est le cardinal d'un
    segment initial de (a,Ro) » :

        ( c ≤ a )  ⇒  (∃t)( t∈a  et  Card(seg(a,Ro,t)) = c ).

    C'est `HTP.realisation_segment` aux binders c='x', t='xw' (ceux qui apparaissent
    dans la décharge `hyp_transport_corps_preuve`).  ⚠️ NON PROUVÉ ICI — théorème de
    représentation ordinal (effondrement de Mostowski), isolé en HYPOTHÈSE, JAMAIS
    postulé.  c≤a fournit F:c→a injective ; B:=image(F)⊂a, bien ordonné par Ro|B, est
    order-iso à un segment initial seg(a,Ro,t), d'où Card(seg(a,Ro,t))=Card(B)=c."""
    return HTP.realisation_segment(Ro, a, c, t)


def realisation_hypothese(Ro="Ro", a="a", c="x", t="xw"):
    """La forme EXACTE de l'hypothèse RÉSIDUELLE de
    `bon_ordre_intervalle_depuis_realisation` (test miroir) :

        (∀c) realisation_segment(Ro,a,c)   [binder c='x', t='xw' — Ro-indépendante]."""
    cn = c if isinstance(c, str) else c.nom
    return pourtout(cn, realisation_segment(Ro, a, cn, t))


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE A — la CLAUSE de plus petit élément pour un S fixé, SANS liant-TERME :
#  clause_min avec T = variable fraîche « Tpb », pullback ÉLIMINÉ par ∃Tpb.
# ════════════════════════════════════════════════════════════════════════════
def _corps_B(Ro, a, S, T):
    """Le corps B(T) = (((T⊂a et T≠∅) et into(T)) et onto(T)) — la forme du témoin
    pullback de `hyp_transport_corps_preuve`, paramétrée par T (VARIABLE fraîche)."""
    vT, va = _t(T), _t(a)
    Tsub = inclus(vT, va)
    Tne = non(egal(vT, E.VIDE))
    into = BOIO.hyp_realisation_min(Ro, a, S, T, t=_BT)
    onto = BOIO.hyp_realisation_onto(Ro, a, S, T, _BC, _BX)
    return et(et(et(Tsub, Tne), into), onto)


def clause_pour_S_sans_terme(Ro="Ro", a="a", S="S", T=_TPB):
    """⊢ { bo_form(Ro,a),  (∀c) realisation_segment(Ro,a,c),  S⊂[0,a],  S≠∅ }
            ⊢ (∃m)( m∈S et (∀x)( x∈S ⇒ R_induit{m,x} ) ).

    🎯 LA CLAUSE de plus petit pour S, DÉRIVÉE SANS le liant-TERME.  `clause_min_
    intervalle_de_pullback` est appelé avec T = la VARIABLE FRAÎCHE « Tpb » : ses 6
    hypothèses { into, bo_form, onto, S⊂[0,a], Tpb≠∅, Tpb⊂a } sont TOUTES BIEN FORMÉES
    (∀Tpb = chaîne, pas de terme dans un liant).  On décharge les 4 propriétés de Tpb
    via le corps B(Tpb), puis on ÉLIMINE ∃Tpb (Tpb non libre dans la conclusion), le
    témoin (∃Tpb)B(Tpb) étant fourni — pour le pullback PB — par
    `hyp_transport_corps_preuve` (CLOS modulo {S⊂[0,a], S≠∅, realisation}).
    theorie=22.  NON vacueux."""
    va, vT = _t(a), _t(T)
    PB = HTP.pullback(a, Ro, S)
    Tn = T if isinstance(T, str) else T.nom

    cm = BOIO.clause_min_intervalle_de_pullback(Ro, a, S, Tn, m=_BM, x=_BX, c=_BC)
    into = BOIO.hyp_realisation_min(Ro, a, S, Tn, t=_BT)
    onto = BOIO.hyp_realisation_onto(Ro, a, S, Tn, _BC, _BX)
    Tsub = inclus(vT, va)
    Tne = non(egal(vT, E.VIDE))
    B_T = _corps_B(Ro, a, S, Tn)

    # décharger les 4 propriétés de Tpb depuis B(Tpb) décomposé
    HB = N.assume(B_T)
    g1 = conjonction_elim_gauche(HB)          # ((Tsub et Tne) et into)
    onto_p = conjonction_elim_droite(HB)      # onto
    g2 = conjonction_elim_gauche(g1)          # (Tsub et Tne)
    into_p = conjonction_elim_droite(g1)      # into
    Tsub_p = conjonction_elim_gauche(g2)      # Tsub
    Tne_p = conjonction_elim_droite(g2)       # Tne
    cm2 = _dech(cm, Tsub, Tsub_p)
    cm2 = _dech(cm2, Tne, Tne_p)
    cm2 = _dech(cm2, into, into_p)
    cm2 = _dech(cm2, onto, onto_p)            # hyps : { bo_form, S⊂[0,a], B(Tpb) }

    # ÉLIMINER ∃Tpb : B(Tpb) ⇒ concl, puis (∃Tpb)B(Tpb) ⇒ concl
    ex_imp = existe_elimination(N.loi_deduction(B_T, cm2), Tn)
    # témoin (∃Tpb)B(Tpb) : le pullback PB via hyp_transport_corps_preuve
    corps = HTP.hyp_transport_corps_preuve(a, Ro, S)   # B(PB)  [S⊂[0,a], S≠∅, realisation]
    ex_B = N.modus_ponens(corps, N.s5(B_T, PB, Tn))    # (∃Tpb)B(Tpb)
    return N.modus_ponens(ex_B, ex_imp)                # concl  [bo_form, S⊂[0,a], S≠∅, realisation]


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE B — la CLAUSE complète clause_plus_petit(≤_induit,[0,a]) sous {bo_form, real}.
# ════════════════════════════════════════════════════════════════════════════
def clause_plus_petit_depuis_realisation(Ro="Ro", a="a", S="S"):
    """⊢ { bo_form(Ro,a),  (∀c) realisation_segment(Ro,a,c) }
            ⊢ clause_plus_petit( ≤_induit , [0,a] )   [binders X=S, a=m, w=x].

    🎯 Décharge (S⊂[0,a] et S≠∅) sur la clause pour S (PIÈCE A), généralise sur S.
    theorie=22, NON vacueux."""
    va, vS = _t(a), _t(S)
    interv = intervalle_0a(a)
    Ssub = inclus(vS, interv)
    Sne = non(egal(vS, E.VIDE))
    HsS = et(Ssub, Sne)

    cs = clause_pour_S_sans_terme(Ro, a, S, _TPB)   # [bo_form, S⊂[0,a], S≠∅, real]
    HHsS = N.assume(HsS)
    cs2 = _dech(cs, Ssub, conjonction_elim_gauche(HHsS))
    cs2 = _dech(cs2, Sne, conjonction_elim_droite(HHsS))   # [bo_form, real, HsS]
    imp_body = N.loi_deduction(HsS, cs2)                    # HsS ⇒ body  [bo_form, real]
    return N.generalisation(S, imp_body)                   # clause_plus_petit  [bo_form, real]


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE C — bon_ordre_intervalle(a) sous {bo_form(Ro), realisation}.
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_intervalle_sous_bo_form(Ro="Ro", a="a", S="S"):
    """⊢ { bo_form(Ro,a),  (∀c) realisation_segment(Ro,a,c) }
            ⊢ bon_ordre_intervalle(a)   (== est_bien_ordonne(≤_induit,[0,a]), LITTÉRAL).

    🎯 Conjoint la PARTIE ORDRE (relation_ordre_dans_intervalle, CLOSE) et la CLAUSE
    (PIÈCE B).  bo_form(Ro,a) = est_bien_ordonne(_R_de(Ro),a) BIEN FORMÉ (∀Tpb = chaîne).
    theorie=22, conclusion == cible déposée."""
    clause = clause_plus_petit_depuis_realisation(Ro, a, S)   # [bo_form, real]
    rod = relation_ordre_dans_intervalle(a)                   # CLOS
    res = conjonction_intro(rod, clause)
    assert res.conclusion == bon_ordre_intervalle(a), \
        "conclusion ≠ bon_ordre_intervalle(a) déposé"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  PIÈCE D — ZERMELO BIEN FORMÉ : (∃Ro) bo_form(Ro,a)  CLOS, binders alignés.
# ════════════════════════════════════════════════════════════════════════════
def _equiv_refl(f):
    """⊢ f ⇔ f."""
    imp = a_implique_a(f)
    return conjonction_intro(imp, imp)


def _impl_congruence_droite(A, thm_eq_B):
    """⊢ (B ⇔ B')  ⟹  ⊢ (A⇒B) ⇔ (A⇒B').   (impl(A,B)=ou(non A,B) ; ou_congruence.)"""
    return ou_congruence(_equiv_refl(non(A)), thm_eq_B)


def _bo_full_equiv(Rname, e):
    """⊢ est_bien_ordonne(_R_de(R), e, X='S',a='a',w='w')
          ⇔ est_bien_ordonne(_R_de(R), e, X='Tpb',a='ms',w='xw').

    α-renomme les TROIS liants de la clause-minimum (∀S→∀Tpb, ∃a→∃ms, ∀w→∀xw) — la
    partie ordre (binders x,y,z) inchangée.  Renommage innermost-first (w, a, S)."""
    Rf = _R_de(Rname)
    ve = _t(e)
    vS = var("S")
    # ── w → xw ────────────────────────────────────────────────────────────────
    eq_forallw = alpha_pour_tout("w", _BX,
        impl(appartient(var("w"), vS), Rf(var("a"), var("w"))))
    eq_pb = et_congruence_droite(appartient(var("a"), vS), eq_forallw)
    eq_ex = congruence_existe(eq_pb, "a")
    body_a_xw = et(appartient(var("a"), vS),
        pourtout(_BX, impl(appartient(var(_BX), vS), Rf(var("a"), var(_BX)))))
    # ── a → ms ────────────────────────────────────────────────────────────────
    eq_petit = equivalence_transitivite(eq_ex, alpha_existe("a", _BM, body_a_xw))
    CS = et(inclus(vS, ve), non(egal(vS, E.VIDE)))
    eq_forallS = congruence_pour_tout(_impl_congruence_droite(CS, eq_petit), "S")
    petit_ms_xw = existe(_BM, et(appartient(var(_BM), vS),
        pourtout(_BX, impl(appartient(var(_BX), vS), Rf(var(_BM), var(_BX))))))
    # ── S → Tpb ───────────────────────────────────────────────────────────────
    eq_minclause = equivalence_transitivite(eq_forallS,
        alpha_pour_tout("S", _TPB, impl(CS, petit_ms_xw)))
    # lift to full est_bien_ordonne (partie ordre inchangée)
    return et_congruence_droite(est_relation_ordre_dans(Rf, ve), eq_minclause)


def zermelo_bo_form(a="a"):
    """⊢ (∃Ro) bo_form(Ro,a)   où  bo_form(Ro,a) = est_bien_ordonne(_R_de(Ro),a,
       x='x',y='y',z='z', X='Tpb', a='ms', w='xw')   (== BOIO._bo_form_canon(a,Ro,Tpb,ms,xw)).

    🎯 ZERMELO (CLOS, theorie=22) α-renommé aux binders de `bo_form`.  zermelo('Xz')
    donne (∃Rz) est_bien_ordonne(_R_de(Rz),Xz,X='S',a='a',w='w') ; on α-renomme la
    clause-minimum (S→Tpb, a→ms, w→xw) sous le ∃, on renomme ∃Rz→∃Ro, puis on
    généralise sur l'ensemble Xz et on l'instancie au TERME a (binders internes Tpb/
    ms/xw ≠ a ⇒ pas de capture).  CLOS, 0 hypothèse."""
    va = _t(a)
    z = Z.zermelo("Xz", "Mz", "Rz")                 # (∃Rz) bo(_R_de Rz, Xz, S,a,w)  CLOS
    # α-renommer la clause-minimum sous le ∃Rz
    z2 = N.modus_ponens(z, equivalence_avant(
        congruence_existe(_bo_full_equiv("Rz", "Xz"), "Rz")))   # (∃Rz) bo(.., Tpb,ms,xw)
    # ∃Rz → ∃Ro
    z3 = N.modus_ponens(z2, equivalence_avant(
        alpha_existe("Rz", "Ro",
            E.est_bien_ordonne(_R_de("Rz"), var("Xz"), X=_TPB, a=_BM, w=_BX))))
    # généraliser l'ENSEMBLE Xz, instancier au TERME a
    res = instancie(N.generalisation("Xz", z3), va)
    assert res.conclusion == existe("Ro", BOIO._bo_form_canon(a, "Ro", _TPB, _BM, _BX)), \
        "zermelo_bo_form ≠ (∃Ro) bo_form(Ro,a)"
    return res


def zermelo_bo_form_cible(a="a"):
    """ÉNONCÉ-cible (test miroir) : (∃Ro) bo_form(Ro,a)."""
    return existe("Ro", BOIO._bo_form_canon(a, "Ro", _TPB, _BM, _BX))


# ════════════════════════════════════════════════════════════════════════════
#  🎯🎯 LE GATE ℕ — bon_ordre_intervalle(a) réduit au SEUL maillon RÉALISATION.
# ════════════════════════════════════════════════════════════════════════════
def bon_ordre_intervalle_depuis_realisation(a="a", Ro="Ro", S="S"):
    """⊢ { (∀c) realisation_segment(Ro,a,c) }  ⊢  bon_ordre_intervalle(a)
                                                   (== la cible déposée, LITTÉRALEMENT).

    🎯🎯 LE GATE ℕ — bon_ordre_intervalle(a) = est_bien_ordonne(≤_induit,[0,a]) DÉRIVÉ
    de l'UNIQUE hypothèse HONNÊTE `(∀c) realisation_segment(Ro,a,c)`, en CONTOURNANT
    le liant-TERME de hyp_transport_ordinal :

      • bon_ordre_intervalle(a) sous { bo_form(Ro), realisation }  (PIÈCE C) ;
      • bo_form(Ro) DÉCHARGÉ : ZERMELO (zermelo_bo_form, CLOS) ÉLIMINE ∃Ro (bo_form(Ro)
        est BIEN FORMÉ : ∀Tpb = chaîne) ; `realisation` est Ro-INDÉPENDANTE (seg(a,·,t)
        ne porte pas Ro), donc inchangée par l'élimination de ∃Ro.

    HYPOTHÈSE SURVIVANTE UNIQUE : `(∀c) realisation_segment(Ro,a,c)` — le théorème de
    représentation ordinal (cf. RAPPORT), isolé, JAMAIS postulé.  PLUS de liant-TERME,
    PLUS de hyp_transport_ordinal.  theorie_ensembles()=22.  Conclusion == bon_ordre_
    intervalle(a) LITTÉRALEMENT.  NON vacueux."""
    bo = BOIO._bo_form_canon(a, Ro, _TPB, _BM, _BX)           # est_bien_ordonne(_R_de(Ro),a)
    boi = bon_ordre_intervalle_sous_bo_form(Ro, a, S)         # [bo_form, real]
    # ÉLIMINER ∃Ro via Zermelo (bo_form bien formé)
    imp_Ro = N.loi_deduction(bo, boi)                         # bo_form(Ro) ⇒ boi  [real]
    ex_Ro_imp = existe_elimination(imp_Ro, Ro)               # (∃Ro)bo_form(Ro) ⇒ boi  [real]
    res = N.modus_ponens(zermelo_bo_form(a), ex_Ro_imp)      # bon_ordre_intervalle(a)  [real]
    assert res.conclusion == bon_ordre_intervalle(a), \
        "conclusion ≠ bon_ordre_intervalle(a) déposé"
    return res


def bon_ordre_intervalle_depuis_realisation_hypotheses(a="a", Ro="Ro"):
    """L'UNIQUE hypothèse SURVIVANTE ATTENDUE (test miroir) :
       { (∀c) realisation_segment(Ro,a,c) }."""
    return {realisation_hypothese(Ro, a)}


__all__ = [
    "realisation_segment", "realisation_hypothese",
    "clause_pour_S_sans_terme", "clause_plus_petit_depuis_realisation",
    "bon_ordre_intervalle_sous_bo_form",
    "zermelo_bo_form", "zermelo_bo_form_cible",
    "bon_ordre_intervalle_depuis_realisation",
    "bon_ordre_intervalle_depuis_realisation_hypotheses",
]
