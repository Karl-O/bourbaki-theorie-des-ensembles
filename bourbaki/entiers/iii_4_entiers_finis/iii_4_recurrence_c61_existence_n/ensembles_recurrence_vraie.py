"""§III.4 / §III.6.1 — RÉCURRENCE *VRAIE* : clôture CORRECTE de ℕ sous le SEUL résidu
honnête `predecesseur_fini_universel` (Prop. 2 §III.5).

────────────────────────────────────────────────────────────────────────────────
POURQUOI CE MODULE (le défaut corrigé).

La chaîne déposée `ensembles_recurrence_C61.N_collectivise_final` repose sur le REPORT #2
= l'universel NU `(∀c)(∀b) cardinal_pas_entre(b,c)` où
    cardinal_pas_entre(b,c) :=  ( b ≤ c+1 )  ⇒  ( b ≤ c  OU  b = c+1 ).
Cet universel NU est MATHÉMATIQUEMENT FAUX pour b NON cardinal : contre-exemple
c=0, b={{∅}} (singleton ≠ le cardinal 1={∅}) — b≤1 (injection {{∅}}↪{∅}), mais b≤0
FAUX ET b=1 FAUX.  La forme `egal` n'est correcte que pour b CARDINAL.  Symétriquement,
le prédicat d'induction NU `P[c]=(∀b)(b≤c⇒Fini b)` est lui-même FAUX (même contre-exemple :
b={{∅}}≤1 mais Fini b faux, car Fini b = est_cardinal(b) ∧ b≠b+1 EXIGE est_cardinal(b)).
Et l'universel NU `(∀a)(∀x) fini_downward(a,x)` que consomme `N_collectivise` est FAUX
pour les mêmes raisons.  La chaîne déposée ne peut donc JAMAIS clore en l'état.

────────────────────────────────────────────────────────────────────────────────
ROUTE RETENUE — B : récurrence sur les CARDINAUX + transport par Card.

On mène la récurrence (métathéorème générique `principe_recurrence_preuve`) sur le
prédicat GARDÉ — VRAI et CLOS à chaque étape — :

    P'[c] := (∀b)( ( est_cardinal(b)  et  b ≤ c ) ⇒ Fini b ).

  • BASE  P'[0]      : base_P0 (b≤0 ⇒ Fini b, INCONDITIONNEL) restreint sous la garde. CLOS.
  • PAS   P'[c]⇒P'[c+1] sous Fini c :  pour b avec est_cardinal(b) ∧ b≤c+1, la garde
        est_cardinal(b) FOURNIT EXACTEMENT l'hypothèse du LEMME N gardé VRAI
        `cardinal_pas_entre_univ` (CLOS) ⇒ b≤c OU b=c+1 ; branche b≤c ⇒ Fini b (P'[c] à b,
        garde rejouée) ; branche b=c+1 ⇒ Fini(c+1) (Fini c via P'[c] à c, garde = est_cardinal(c)
        ISSU de Fini c ; puis fini_implique_fini_successeur).  CLOS.
  • RÉCURRENCE : `principe_recurrence_preuve(P', c)` (générique, plus-petit-contre-exemple)
        ⇒ principe_recurrence(P', c) sous le SEUL résidu `predecesseur_fini_universel`.
        Avec P'[0] et le pas (CLOS) ⇒ (∀c)( Fini c ⇒ P'[c] )  [résidu : pfu].

  • TRANSPORT (général a, x) :  pour a CARDINAL, fini_downward(a,x)=(a≤x ∧ Fini x)⇒Fini a
        est VRAI et DÉRIVÉ :  Fini x ⇒ est_cardinal(x) ⇒ Card x = x ; a≤x ⇒ Card a≤Card x
        (inf_egal_transporte_cardinal, CLOS) ; Fini x ⇒ Fini(Card x) (Leibniz x=Card x) ;
        P'[Card x] (récurrence à c:=Card x) instancié à b:=Card a, avec est_cardinal(Card a)
        (card_est_un_cardinal) et Card a≤Card x ⇒ Fini(Card a) ; Card a=a (cardinal_de_cardinal,
        a CARDINAL) ⇒ Fini a (Leibniz).  La garde est_cardinal(a) est INDISPENSABLE et VRAIE
        sous le témoin a:=Card X.

  • ℕ EXISTE :  `cardinal_infini_existe_card` (de A4, CLOS) donne le témoin INFINI a=Card X
        AVEC est_cardinal(a) ∧ ¬Fini(a).  On RÉUTILISE `N_collectivise_sous_cardinal`
        (coll sous {¬Fini(a), (∀x)fini_downward(a,x)}), on décharge (∀x)fini_downward(a,x)
        par le transport gardé (sous est_cardinal(a) + pfu), puis on décharge la conjonction
        (est_cardinal(a) ∧ ¬Fini a) et on élimine le témoin a.  ⇒ coll(x, Fini x)  [résidu : pfu].

────────────────────────────────────────────────────────────────────────────────
⚠️ INVARIANTS.  theorie_ensembles() = 22 intangible (rien postulé ; le seul axiome utilisé
   est celui de Ncol, en théorie DÉDIÉE, via N_collectivise — inchangé).  RÉSIDU UNIQUE :
   `predecesseur_fini_universel` (Prop. 2 §III.5, gap MATHÉMATIQUE non clos).  Le report #2
   FAUX est ÉLIMINÉ : sa forme correcte (gardée) `cardinal_pas_entre_univ` est CLOSE et la
   garde est_cardinal(b) est FOURNIE par P'.  On NE modifie PAS ensembles_recurrence_C61
   (chaîne PARALLÈLE).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, ou, non, impl, existe, pourtout, subst_f,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card, cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    contraposition, cas, instancie, equivalence_avant, composantes_conjonction,
    antecedent_consequent,
)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie

# ── briques CLOSES réutilisées ────────────────────────────────────────────────
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    base_P0, recurrence_C61, principe_recurrence, _fini_implique_P,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.cardinaux.ensembles_cardinal_pas_entre_univ import cardinal_pas_entre_univ
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
    fini_implique_fini_successeur, cardinal_de_cardinal,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
    fini_implique_cardinal, card_est_un_cardinal,
)
from bourbaki.cardinaux.arithmetique.iii_3_2_monotonie.ensembles_arith_cardinale_props_exposant_monotone import (
    inf_egal_transporte_cardinal,
)
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini_ensemble, A4, theorie_infini
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (
    fini_downward, N_collectivise_sous_cardinal, _coll_fini,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ════════════════════════════════════════════════════════════════════════════
#  PRÉDICAT D'INDUCTION GARDÉ — VRAI et CLOS à chaque étape.
# ════════════════════════════════════════════════════════════════════════════
def _Pp(c, b="b"):
    """P'[c] := (∀b)( ( est_cardinal(b) et b ≤ c ) ⇒ Fini b ).

    Version GARDÉE (correcte) du prédicat d'induction : « tout CARDINAL ≤ c est fini ».
    Contrairement à la forme NUE (∀b)(b≤c⇒Fini b) — FAUSSE pour b non cardinal — celle-ci
    est VRAIE (la garde est_cardinal(b) est INTRINSÈQUE, cf. cardinal_pas_entre_univ)."""
    vc = _t(c)
    vb = var(b)
    return pourtout(b, impl(et(est_cardinal(vb), inf_egal_card(vb, vc)), est_fini(vb)))


def _Pp_pred(b="b"):
    """Le prédicat P' comme fonction Terme → Formule (pour le métathéorème générique)."""
    return lambda t: _Pp(t, b)


# ════════════════════════════════════════════════════════════════════════════
#  BASE  P'[0]  (INCONDITIONNEL, CLOS).
# ════════════════════════════════════════════════════════════════════════════
def preuve_P0_vrai(b="b"):
    """⊢ P'[0] = (∀b)( ( est_cardinal(b) et b ≤ 0 ) ⇒ Fini b ).   (INCONDITIONNEL, CLOS.)

    base_P0 (b≤0 ⇒ Fini b, INCONDITIONNEL) restreint sous la garde : on PROJETTE b≤0
    de l'antécédent gardé, on applique base_P0, on regénéralise."""
    vb = var(b)
    bp0 = base_P0(b)                                       # (b≤0) ⇒ Fini b
    garde = et(est_cardinal(vb), inf_egal_card(vb, ZERO))
    h = N.assume(garde)
    le0 = conjonction_elim_droite(h)                       # b ≤ 0
    fin = N.modus_ponens(le0, bp0)                         # Fini b
    return N.generalisation(b, N.loi_deduction(garde, fin))   # P'[0]


# ════════════════════════════════════════════════════════════════════════════
#  PAS  (∀c)( ( Fini c et P'[c] ) ⇒ P'[c+1] )  (CLOS).
# ════════════════════════════════════════════════════════════════════════════
def preuve_step_vrai(c="c", b="b"):
    """⊢ (∀c)( ( Fini c et P'[c] ) ⇒ P'[c+1] ).   (CLOS — la garde de P' fournit
    l'hypothèse VRAIE du LEMME N gardé `cardinal_pas_entre_univ`.)

    Pour b avec est_cardinal(b) ∧ b≤c+1 :
      cardinal_pas_entre_univ (CLOS, gardé par est_cardinal(b) — DISPONIBLE) ⇒ b≤c OU b=c+1 :
        • b≤c   : Fini b par P'[c] à b (garde est_cardinal(b) rejouée) ;
        • b=c+1 : Fini c par P'[c] à c (garde est_cardinal(c) ISSUE de Fini c, c≤c réflexif),
                  puis Fini(c+1) (fini_implique_fini_successeur), puis Leibniz c+1↦b."""
    vc, vb = var(c), var(b)
    succ_c = successeur(vc)
    Pc = _Pp(vc, b)
    garde_c = lambda t: et(est_cardinal(t), inf_egal_card(t, vc))         # est_cardinal(·) et ·≤c
    garde_succ = lambda t: et(est_cardinal(t), inf_egal_card(t, succ_c))  # est_cardinal(·) et ·≤c+1

    h_conj = N.assume(et(est_fini(vc), Pc))                # Fini c et P'[c]
    fini_c = conjonction_elim_gauche(h_conj)               # Fini c
    hPc = conjonction_elim_droite(h_conj)                  # P'[c]
    card_c = conjonction_elim_gauche(fini_c)               # est_cardinal(c)  (1er conjoint de Fini c)

    inst_b = instancie(hPc, vb)                            # (est_cardinal(b) et b≤c) ⇒ Fini b
    inst_c = instancie(hPc, vc)                            # (est_cardinal(c) et c≤c) ⇒ Fini c
    refl_all = N.generalisation("X", inf_egal_reflexif("X"))
    c_le_c = instancie(refl_all, vc)                       # c ≤ c
    fini_c2 = N.modus_ponens(conjonction_intro(card_c, c_le_c), inst_c)        # Fini c  (via P'[c])
    fini_succ_c = N.modus_ponens(fini_c2, fini_implique_fini_successeur(vc))   # Fini(c+1)

    # LEMME N gardé VRAI : est_cardinal(b) ⇒ ( (b≤c+1) ⇒ (b≤c ou b=c+1) )
    cpe_univ = cardinal_pas_entre_univ("b", "c")           # (∀c)(∀b)( est_cardinal(b) ⇒ cardinal_pas_entre(b,c) )
    cpe_bc = instancie(instancie(cpe_univ, vc), vb)        # est_cardinal(b) ⇒ cardinal_pas_entre(b,c)

    h_garde_succ = N.assume(garde_succ(vb))                # est_cardinal(b) et b≤c+1
    card_b = conjonction_elim_gauche(h_garde_succ)         # est_cardinal(b)
    le_succ = conjonction_elim_droite(h_garde_succ)        # b ≤ c+1
    sub_b = N.modus_ponens(card_b, cpe_bc)                 # (b≤c+1) ⇒ (b≤c ou b=c+1)
    disj = N.modus_ponens(le_succ, sub_b)                  # b≤c ou b=c+1

    # branche b≤c
    h_le_c = N.assume(inf_egal_card(vb, vc))               # b ≤ c
    fini_b_left = N.modus_ponens(conjonction_intro(card_b, h_le_c), inst_b)    # Fini b
    branch_left = N.loi_deduction(inf_egal_card(vb, vc), fini_b_left)
    # branche b=c+1
    h_eq = N.assume(egal(vb, succ_c))                      # b = c+1
    succ_eq_b = N.modus_ponens(h_eq, symetrie(vb, succ_c)) # c+1 = b
    leib = N.s6(succ_c, vb, "w", est_fini(var("w")))       # (c+1=b) ⇒ (Fini(c+1) ⇔ Fini b)
    eqv = N.modus_ponens(succ_eq_b, leib)
    fini_b_right = N.modus_ponens(fini_succ_c, equivalence_avant(eqv))         # Fini b
    branch_right = N.loi_deduction(egal(vb, succ_c), fini_b_right)

    fini_b = cas(disj, branch_left, branch_right)          # Fini b
    corps_succ = N.loi_deduction(garde_succ(vb), fini_b)   # (est_cardinal(b) et b≤c+1) ⇒ Fini b
    Pc1 = N.generalisation(b, corps_succ)                  # P'[c+1]
    step_imp = N.loi_deduction(et(est_fini(vc), Pc), Pc1)  # (Fini c et P'[c]) ⇒ P'[c+1]
    return N.generalisation(c, step_imp)                   # (∀c)((Fini c et P'[c]) ⇒ P'[c+1])


# ════════════════════════════════════════════════════════════════════════════
#  RÉCURRENCE  ⊢ { predecesseur_fini_universel } ⊢ (∀c)( Fini c ⇒ P'[c] ).
# ════════════════════════════════════════════════════════════════════════════
def recurrence_fini_implique_P_vrai(c="c", b="b"):
    """⊢ { predecesseur_fini_universel } ⊢ (∀c)( Fini c ⇒ P'[c] ).

    Métathéorème C61 GÉNÉRIQUE (`principe_recurrence_preuve`, plus-petit-contre-exemple)
    appliqué au prédicat GARDÉ P' = _Pp_pred(b), avec la base et le pas CLOS ci-dessus.
    Le SEUL résidu honnête est `predecesseur_fini_universel` (Prop. 2 §III.5) — toute la
    structure inductive (bon ordre + séparation + pas) est mécanisée et close."""
    P = _Pp_pred(b)
    p0 = preuve_P0_vrai(b)                                 # ⊢ P'[0]   (CLOS)
    step = preuve_step_vrai(c, b)                          # ⊢ pas     (CLOS)
    rec = recurrence_C61(p0, step, P, c)                   # (∀c)(Fini c ⇒ P'[c])  [hyp principe_recurrence(P,c)]
    princ = principe_recurrence(P, c)
    preuve_princ = principe_recurrence_preuve(P, c)        # ⊢ principe_recurrence(P,c)  [pfu]
    assert preuve_princ.conclusion == princ, "principe_recurrence_preuve ne conclut pas le principe pour P'"
    res = _cut(rec, princ, preuve_princ)                  # (∀c)(Fini c ⇒ P'[c])  [pfu]
    assert res.conclusion == _fini_implique_P(P, c), "récurrence : conclusion ≠ (∀c)(Fini c ⇒ P'[c])"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  TRANSPORT — fini_downward(a,x) pour a CARDINAL  (VRAI, DÉRIVÉ).
# ════════════════════════════════════════════════════════════════════════════
def _fini_downward_garde(rec_thm, a="a", x="x"):
    """De `rec_thm` ⊢ (∀c)(Fini c ⇒ P'[c]) [pfu], produit
       ⊢ { est_cardinal(a), [hyps de rec_thm] } ⊢ fini_downward(a,x)
         = ( a ≤ x  et  Fini x )  ⇒  Fini a.

    Sous a CARDINAL (garde, VRAIE pour le témoin a=Card X), Fini x ⇒ est_cardinal(x) ⇒
    Card x = x ; a≤x ⇒ Card a ≤ Card x (transport CLOS) ; Fini x ⇒ Fini(Card x) ; P'[Card x]
    (récurrence) instancié à b:=Card a avec est_cardinal(Card a) ⇒ Fini(Card a) ; Card a=a
    (a cardinal) ⇒ Fini a.  La garde est_cardinal(a) est INDISPENSABLE (cf. contre-exemple
    b={{∅}} pour la forme non gardée)."""
    va, vx = _t(a), _t(x)
    cA, cX = cardinal(va), cardinal(vx)
    h_card_a = N.assume(est_cardinal(va))                  # est_cardinal(a)   [hyp]
    ante = et(inf_egal_card(va, vx), est_fini(vx))
    h_dwn = N.assume(ante)                                 # a≤x et Fini x
    le_ax = conjonction_elim_gauche(h_dwn)                 # a ≤ x
    fini_x = conjonction_elim_droite(h_dwn)                # Fini x
    card_x = N.modus_ponens(fini_x, fini_implique_cardinal(vx))   # est_cardinal(x)

    cardA_eq_a = N.modus_ponens(h_card_a, cardinal_de_cardinal(va))   # Card a = a
    cardX_eq_x = N.modus_ponens(card_x, cardinal_de_cardinal(vx))     # Card x = x
    x_eq_cardX = N.modus_ponens(cardX_eq_x, symetrie(cX, vx))         # x = Card x

    le_cards = N.modus_ponens(le_ax, inf_egal_transporte_cardinal(va, vx))  # Card a ≤ Card x

    # Fini(Card x) via x = Card x  (Leibniz x ↦ Card x dans Fini(·))
    leib_x = N.s6(vx, cX, "wx", est_fini(var("wx")))       # (x=Card x) ⇒ (Fini x ⇔ Fini(Card x))
    fini_cardX = N.modus_ponens(fini_x,
                                equivalence_avant(N.modus_ponens(x_eq_cardX, leib_x)))   # Fini(Card x)

    # récurrence @ c := Card x : Fini(Card x) ⇒ P'[Card x]
    rec_at_cardX = instancie(rec_thm, cX)                  # Fini(Card x) ⇒ P'[Card x]
    Pp_cardX = N.modus_ponens(fini_cardX, rec_at_cardX)    # P'[Card x] = (∀b)((est_card(b) et b≤Card x) ⇒ Fini b)
    inst_b = instancie(Pp_cardX, cA)                       # (est_card(Card a) et Card a≤Card x) ⇒ Fini(Card a)
    # le 1er conjoint de l'antécédent (est_cardinal(Card a)) fixe le liant interne attendu
    # (« X » par défaut de est_cardinal, ≠ « X' » de card_est_un_cardinal) — on l'aligne EXACTEMENT.
    ante_b, _cons_b = antecedent_consequent(inst_b.conclusion)
    L_card, _R_le = composantes_conjonction(ante_b)        # L_card = est_cardinal(Card a) attendu
    card_cardA = card_est_un_cardinal(va, lieur=L_card.lieur)   # est_cardinal(Card a)  (liant aligné)
    assert card_cardA.conclusion == L_card, "est_cardinal(Card a) : liant non aligné sur P'"
    fini_cardA = N.modus_ponens(conjonction_intro(card_cardA, le_cards), inst_b)   # Fini(Card a)

    # Fini a via Card a = a  (Leibniz Card a ↦ a dans Fini(·))
    leib_a = N.s6(cA, va, "wa", est_fini(var("wa")))       # (Card a=a) ⇒ (Fini(Card a) ⇔ Fini a)
    fini_a = N.modus_ponens(fini_cardA,
                            equivalence_avant(N.modus_ponens(cardA_eq_a, leib_a)))   # Fini a

    res = N.loi_deduction(ante, fini_a)                    # (a≤x et Fini x) ⇒ Fini a
    assert res.conclusion == fini_downward(va, vx), "transport : conclusion ≠ fini_downward(a,x)"
    return res


def fini_downward_garde_thm(a="a", x="x", c="c", b="b"):
    """⊢ { est_cardinal(a), predecesseur_fini_universel } ⊢ (∀x) fini_downward(a, x).

    La downward-closure de Fini POUR UN CARDINAL a (≠ l'universel NU FAUX (∀a)(∀x)…) :
    le transport gardé `_fini_downward_garde` régénéralisé sur x.  Le SEUL résidu est
    `predecesseur_fini_universel` (via la récurrence) + la garde est_cardinal(a)."""
    rec = recurrence_fini_implique_P_vrai(c, b)            # (∀c)(Fini c ⇒ P'[c])  [pfu]
    dwn = _fini_downward_garde(rec, a, x)                  # fini_downward(a,x)  [est_cardinal(a), pfu]
    return N.generalisation(x, dwn)                        # (∀x) fini_downward(a,x)


# ════════════════════════════════════════════════════════════════════════════
#  ℕ EXISTE — un cardinal infini AVEC sa qualité de cardinal (de A4, CLOS).
# ════════════════════════════════════════════════════════════════════════════
def cardinal_infini_existe_card(a="a", X="X"):
    """⊢ (∃a)( est_cardinal(a) et ¬Fini(a) ).   (de A4 ; CLOS, témoin a := Card X.)

    Renforcement de `cardinal_infini_existe` (qui ne donne que (∃a)¬Fini a) : on conjoint
    est_cardinal(a).  Le témoin Card X EST un cardinal (card_est_un_cardinal, CLOS) et
    vérifie ¬Fini(Card X) (corps de A4).  Le pont captured/uncaptured (BRIDGE Fini_unc ⇒
    Fini_cap, 2e conjoint identique, 1er conjoint est_cardinal PROUVÉ) reprend celui de
    cardinal_infini_existe.  Nécessaire pour décharger LA GARDE est_cardinal(a) du transport
    SOUS le témoin (sinon a serait libre dans l'élimination du témoin)."""
    vX = var(X)
    cX = cardinal(vX)
    va = var(a)
    body = et(est_cardinal(va), non(est_fini(va)))         # est_cardinal(a) et ¬Fini(a)
    target_unc = subst_f(cX, a, body)                      # (Card X | a) body   (binders internes α-sûrs)
    card_unc, notfini_unc = composantes_conjonction(target_unc)
    fini_unc = notfini_unc.sous[0]                         # Fini_unc(Card X)
    A4body = est_infini_ensemble(vX)                       # ¬Fini_cap(Card X)  (= corps de A4)
    fini_cap = A4body.sous[0]                              # Fini_cap(Card X)
    c1cap, _c2cap = composantes_conjonction(fini_cap)      # est_cardinal_cap(Card X), Card X≠Card X+1
    # est_cardinal_unc(Card X)  (binder de la forme uncaptured)
    card_cardX = card_est_un_cardinal(X, lieur=card_unc.lieur)
    assert card_cardX.conclusion == card_unc, "est_cardinal_unc : forme inattendue"
    # BRIDGE Fini_unc ⇒ Fini_cap  (1er conjoint est_cardinal_cap PROUVÉ, 2e conjoint identique)
    card_cap_proof = card_est_un_cardinal(X, lieur=c1cap.lieur)
    assert card_cap_proof.conclusion == c1cap, "est_cardinal_cap : forme inattendue"
    h_unc = N.assume(fini_unc)
    c2_thm = conjonction_elim_droite(h_unc)                # Card X ≠ Card X+1
    fini_cap_thm = conjonction_intro(card_cap_proof, c2_thm)   # Fini_cap(Card X)  [Fini_unc]
    imp_unc_cap = N.loi_deduction(fini_unc, fini_cap_thm)  # Fini_unc ⇒ Fini_cap
    bridge = contraposition(imp_unc_cap)                   # ¬Fini_cap ⇒ ¬Fini_unc
    # sous le témoin X : A4body=¬Fini_cap ⊢ ¬Fini_unc ⊢ body_unc ⊢ (∃a)body
    hbody = N.assume(A4body)                               # ¬Fini_cap(Card X)
    notfini_unc_thm = N.modus_ponens(hbody, bridge)        # ¬Fini_unc(Card X)
    body_unc_thm = conjonction_intro(card_cardX, notfini_unc_thm)   # target_unc
    assert body_unc_thm.conclusion == target_unc, "body_unc : forme inattendue"
    ex_a = N.modus_ponens(body_unc_thm, N.s5(body, cX, a)) # (∃a) body  [A4body]
    wit = N.loi_deduction(A4body, ex_a)                    # A4body ⇒ (∃a)body
    exX = existe_elimination(wit, X)                       # (∃X)A4body ⇒ (∃a)body
    a4 = N.axiome(theorie_infini(), A4)                    # (∃X)¬Fini(Card X) = A4
    return N.modus_ponens(a4, exX)                         # (∃a)( est_cardinal(a) et ¬Fini a )


# ════════════════════════════════════════════════════════════════════════════
#  🎯 THÉORÈME 1 (E.III.6.1) — ℕ EXISTE, sous le SEUL résidu honnête pfu.
# ════════════════════════════════════════════════════════════════════════════
def N_collectivise_vrai(a="a", x="x", c="c", b="b", Y="y"):
    """🎯 ⊢ { predecesseur_fini_universel } ⊢ coll(x, Fini x).

    THÉORÈME 1, E.III.6.1 — « Fini(x) est collectivisante » (l'ensemble ℕ des entiers
    naturels EXISTE), avec pour UNIQUE report le résidu honnête `predecesseur_fini_universel`
    (Prop. 2 §III.5 : tout entier ≠0 est un successeur ; gap MATHÉMATIQUE non clos).  Le
    report #2 FAUX de la chaîne déposée (universel NU cardinal_pas_entre) est ÉLIMINÉ :
    on mène la récurrence sur le prédicat GARDÉ VRAI P' (cardinal_pas_entre_univ CLOS) et on
    transporte aux ENSEMBLES généraux via Card.

    Assemblage (mirroir de N_collectivise) :
      • `cardinal_infini_existe_card` (de A4, CLOS) ⊢ (∃a)( est_cardinal(a) et ¬Fini a ) ;
      • sous le témoin a : `N_collectivise_sous_cardinal` donne coll sous {¬Fini a, (∀x)fini_downward(a,x)} ;
      • on décharge (∀x)fini_downward(a,x) par `fini_downward_garde_thm` (sous est_cardinal(a)+pfu) ;
      • on décharge la conjonction (est_cardinal(a) et ¬Fini a) ⇒ coll, on élimine le témoin a
        (PROPRE : non libre dans coll ni dans pfu), MP avec l'existence ⇒ coll.
    theorie=22, rien postulé."""
    va, vx = var(a), var(x)
    # coll sous {¬Fini a, (∀x)fini_downward(a,x)}  (a variable PROPRE)
    sub = N_collectivise_sous_cardinal(a, x, Y)            # hyps : ¬Fini(a), (∀x)fini_downward(a,x)
    # décharge (∀x)fini_downward(a,x) par le transport gardé (sous est_cardinal(a) + pfu)
    dwn_all = pourtout(x, fini_downward(va, vx))           # (∀x)fini_downward(a,x)
    fd = fini_downward_garde_thm(a, x, c, b)               # ⊢ (∀x)fini_downward(a,x)  [est_cardinal(a), pfu]
    assert fd.conclusion == dwn_all, "fini_downward_garde_thm ne conclut pas (∀x)fini_downward(a,x)"
    coll_sous_ab = _cut(sub, dwn_all, fd)                 # coll  [¬Fini a, est_cardinal(a), pfu]
    # décharge la conjonction (est_cardinal a et ¬Fini a)
    conj = et(est_cardinal(va), non(est_fini(va)))
    h_conj = N.assume(conj)
    card_a = conjonction_elim_gauche(h_conj)              # est_cardinal(a)
    nfin_a = conjonction_elim_droite(h_conj)              # ¬Fini(a)
    coll1 = _cut(coll_sous_ab, est_cardinal(va), card_a)  # coll  [¬Fini a, conj, pfu]
    coll2 = _cut(coll1, non(est_fini(va)), nfin_a)        # coll  [conj, pfu]
    wit = N.loi_deduction(conj, coll2)                    # (est_cardinal a et ¬Fini a) ⇒ coll  [pfu]
    ex_imp = existe_elimination(wit, a)                   # (∃a)(est_cardinal a et ¬Fini a) ⇒ coll  [pfu]
    exists_inf = cardinal_infini_existe_card(a, "X")      # (∃a)(est_cardinal a et ¬Fini a)  (A4, CLOS)
    res = N.modus_ponens(exists_inf, ex_imp)              # coll(x, Fini x)  [pfu]
    assert res.conclusion == _coll_fini(x), "N_collectivise_vrai : conclusion ≠ coll(x, Fini x)"
    return res


__all__ = [
    "preuve_P0_vrai", "preuve_step_vrai", "recurrence_fini_implique_P_vrai",
    "fini_downward_garde_thm", "cardinal_infini_existe_card",
    "N_collectivise_vrai",
]
