"""§III.5.1 — Corollaire 3 : la PUISSANCE de deux entiers est un entier.

🎯 BUT (G2)  ⊢ ( Fini a et Fini b ) ⇒ Fini( a^b ).

Miroir EXACT de `produit_binaire_entier` (ensembles_prop3_produit_entier_iii5) et de
`somme_binaire_entier` (ensembles_combinatoire_iii5) pour la PUISSANCE : récurrence
C61 sur l'exposant b avec P[b] := Fini(a^b), sous Fini a :
    • P[0] : a^0 = Card({∅}) = 1 — fini  (exposant_zero_egale_un + fini_un) ;
    • P[n] ⇒ P[n+1] : a^(n+1) = a^n · a  (MAILLON `puissance_succ_eq`) ; Fini(a^n)
      et Fini a ⇒ Fini(a^n · a)  (produit_binaire_entier = G1, REUTILISÉ).
C61 (principe_recurrence_preuve, résidu prédécesseur DÉCHARGÉ) donne
(∀b)(Fini b ⇒ Fini(a^b)).

────────────────────────────────────────────────────────────────────────────────
⚠️ LE MAILLON ALGÉBRIQUE  a^(n+1) = a^n · a  (puissance_succ_eq) :

    a^(n+1) = Card(𝓕(n+1; a))            [déf, n+1 = successeur n = Card(n⊔{∅})]
            = Card(𝓕(n⊔{∅}; a))          [(B) EXPONENT-INVARIANCE — voir ci-dessous]
            = Card(𝓕(n;a) × 𝓕({∅};a))    [prop9_close(a,n,{∅}), forme exponentielle]
            = a^n · a                      [produit bien-défini + a^1=a (exposant_un_egale)]

Le pas (B) « EXPONENT-INVARIANCE » est l'UNIQUE point non disponible dans le dépôt :
        Card(𝓕(Card(n⊔{∅}); a)) = Card(𝓕(n⊔{∅}; a)),
car le successeur n+1 := Card(n⊔{∅}) est le CARDINAL de n⊔{∅} (≠ l'ensemble n⊔{∅}
littéral).  C'est le KEYSTONE manquant `eq_exposant_invariant` :

        Eq(X, Y)  ⇒  Eq( 𝓕(X; a),  𝓕(Y; a) )        (précomposition par la bijection)

— l'analogue, pour les espaces de fonctions, de `eq_produit_invariant` (déjà clos
pour le produit).  Sa construction (bijection g ↦ g∘φ de 𝓕(X;a) sur 𝓕(Y;a) à
partir d'une bijection φ:Y→X, avec toute la machinerie graphe fonctionnel / domaine
/ injective / image) est un chantier comparable à une direction de la Prop. 9 et
N'EST PAS encore dans le dépôt.

On EXPOSE donc (B) comme une HYPOTHÈSE EXPLICITE, NON circulaire (elle porte sur les
SUPPORTS — l'équipotence d'espaces de fonctions — la conclusion sur leurs CARDINAUX),
exactement comme `exposant_monotone_base_conditionnel` /
`exposant_monotone_exposant_conditionnel` (déjà acceptés dans le dépôt).  Le maillon
et la clôture de la récurrence sont alors CERTIFIÉS sous cette seule hypothèse de
support ; sa décharge = construction de `eq_exposant_invariant` (REPORTÉE, isolée).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, impl
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_arriere, equivalence_avant,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_bien_defini,
)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.prop9_exp_somme.ensembles_prop9_final_close import prop9_close
from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.exposant_un._bijection import (
    exposant_un_egale,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import produit_binaire_entier
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _pcbd_t(tX, tY, ta, tb):
    """produit_cardinal_bien_defini version TERME capture-safe (généralise+instancie)."""
    g = produit_cardinal_bien_defini("Xpcbd", "Ypcbd", "apcbd", "bpcbd")
    gen = N.generalisation("Xpcbd", N.generalisation("Ypcbd",
          N.generalisation("apcbd", N.generalisation("bpcbd", g))))
    return instancie(instancie(instancie(instancie(gen, _t(tX)), _t(tY)), _t(ta)), _t(tb))


# ══════════════════════════════════════════════════════════════════════════════
#  (B)  EXPONENT-INVARIANCE — l'énoncé du keystone manquant `eq_exposant_invariant`
# ══════════════════════════════════════════════════════════════════════════════
def exposant_invariance_enonce(a="Aexi", n="Nexi"):
    """L'ÉNONCÉ (formule) du pas (B), exposé comme HYPOTHÈSE de support du maillon :

        Card(𝓕(n+1; a)) = Card(𝓕(n⊔{∅}; a)),

    i.e. a^(n+1) = Card(𝓕(n⊔{∅}; a)).  (n+1 := successeur n = Card(n⊔{∅}).)

    NON circulaire : porte sur l'égalité des CARDINAUX de deux espaces de fonctions
    équipotents (le successeur étant le cardinal de n⊔{∅}).  Sa preuve = le keystone
    `eq_exposant_invariant : Eq(X,Y) ⇒ Eq(𝓕(X;a),𝓕(Y;a))` (REPORTÉ)."""
    va, vn = _t(a), _t(n)
    sing = E.singleton(E.VIDE)
    n_sing = somme_disjointe(vn, sing)              # n ⊔ {∅}
    succ_n = successeur(vn)                           # n+1 = Card(n⊔{∅})
    lhs = exposant_cardinal_binaire(va, succ_n)      # a^(n+1) = Card(𝓕(n+1;a))
    rhs = cardinal(E.applications(n_sing, va))        # Card(𝓕(n⊔{∅};a))
    return egal(lhs, rhs)


# ══════════════════════════════════════════════════════════════════════════════
#  MAILLON ALGÉBRIQUE — a^(n+1) = a^n · a   (sous (B) + a, n cardinaux)
# ══════════════════════════════════════════════════════════════════════════════
def puissance_succ_eq(a="Apse", n="Npse"):
    """⊢ exposant_invariance_enonce(a,n) ⇒
            ( (est_cardinal a et est_cardinal n) ⇒ a^(n+1) = a^n · a ).

    Le MAILLON de récurrence (Cor. Prop. 9 §III.3.5), CERTIFIÉ sous la SEULE
    hypothèse de support (B).  Chaîne :
        a^(n+1) = Card(𝓕(n⊔{∅};a))         [(B), hyp]
                = Card(𝓕(n;a) × 𝓕({∅};a))   [prop9_close(a,n,{∅})]
                = Card(𝓕(n;a)) · Card(a)     [produit bien-défini ; a^1=a]
                = a^n · a."""
    va, vn = _t(a), _t(n)
    sing = E.singleton(E.VIDE)                       # {∅}
    n_sing = somme_disjointe(vn, sing)               # n ⊔ {∅}
    succ_n = successeur(vn)                            # n+1

    Fn = E.applications(vn, va)                        # 𝓕(n;a)         (support de a^n)
    Fsing = E.applications(sing, va)                  # 𝓕({∅};a)       (support de a^1)
    an = exposant_cardinal_binaire(va, vn)            # a^n = Card(𝓕(n;a))
    lhs = exposant_cardinal_binaire(va, succ_n)       # a^(n+1)
    rhs_prod = produit_cardinal_binaire(an, va)       # a^n · a

    hB = N.assume(exposant_invariance_enonce(va, vn))  # a^(n+1) = Card(𝓕(n⊔{∅};a))

    hcard = N.assume(et(est_cardinal(va), est_cardinal(vn)))

    # (1)  prop9_close(a, n, {∅}) :
    #      Card(𝓕(n⊔{∅};a)) = Card(𝓕(n;a) × 𝓕({∅};a))
    p9 = prop9_close(va, vn, sing)
    eq_p9 = p9                                         # Card(𝓕(n⊔{∅};a)) = Card(Fn×Fsing)
    card_nsing = cardinal(E.applications(n_sing, va))
    card_prod = cardinal(E.produit(Fn, Fsing))
    assert eq_p9.conclusion == egal(card_nsing, card_prod), "prop9_close : forme inattendue"

    # (2)  a^1 = a   :  Card(𝓕({∅};a)) = Card(a)
    eq_un = exposant_un_egale(va)                     # Card(𝓕({∅};a)) = Card(a)
    card_Fsing = cardinal(Fsing)
    card_a = cardinal(va)
    assert eq_un.conclusion == egal(card_Fsing, card_a), "exposant_un_egale : forme inattendue"

    # (3)  produit bien-défini : (Card(Fn)=a^n et Card(Fsing)=Card a) ⇒
    #         Card(Fn × Fsing) = produit_cardinal_binaire(a^n, Card a)
    #   Card(Fn) == a^n syntaxiquement (déf exposant_cardinal_binaire = Card(𝓕(n;a))).
    refl_an = N.reflexivite(an)                       # Card(𝓕(n;a)) = a^n  (réflexif)
    bd = _pcbd_t(Fn, Fsing, an, card_a)               # (Card Fn=a^n et Card Fsing=Card a) ⇒
                                                      #   Card(Fn×Fsing)=a^n·Card a
    eq_prod = N.modus_ponens(conjonction_intro(refl_an, eq_un), bd)  # Card(Fn×Fsing)=a^n·Card a
    prod_an_carda = produit_cardinal_binaire(an, card_a)

    # (4)  a^n · Card a = a^n · a   (congruence : Card a = a sous est_cardinal a)
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import cardinal_de_cardinal
    ca = conjonction_elim_gauche(hcard)               # est_cardinal a
    gen_cdc = N.generalisation("xcdc", cardinal_de_cardinal("xcdc"))
    cdc = instancie(gen_cdc, va)                      # est_cardinal a ⇒ Card a = a
    card_a_eq_a = N.modus_ponens(ca, cdc)             # Card a = a
    V = produit_cardinal_binaire(an, var("wnpse"))    # a^n · w
    eq4 = N.modus_ponens(card_a_eq_a,
            congruence_terme(card_a, va, V, w="wnpse"))  # a^n·Card a = a^n·a

    # ── ASSEMBLAGE :
    #   a^(n+1) =[B] Card(𝓕(n⊔{∅};a)) =[p9] Card(Fn×Fsing) =[bd] a^n·Card a =[4] a^n·a
    chain1 = composer_egalites(hB, eq_p9)             # a^(n+1) = Card(Fn×Fsing)
    chain2 = composer_egalites(chain1, eq_prod)       # a^(n+1) = a^n·Card a
    final = composer_egalites(chain2, eq4)            # a^(n+1) = a^n·a
    assert final.conclusion == egal(lhs, rhs_prod), "maillon : conclusion inattendue"

    sous_card = N.loi_deduction(et(est_cardinal(va), est_cardinal(vn)), final)
    out = N.loi_deduction(exposant_invariance_enonce(va, vn), sous_card)
    cible = impl(exposant_invariance_enonce(va, vn),
                 impl(et(est_cardinal(va), est_cardinal(vn)), egal(lhs, rhs_prod)))
    assert out.conclusion == cible, "puissance_succ_eq : conclusion inattendue"
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  BASE CASE BRIDGE (B0) — même nature que (B), à l'exposant 0
# ══════════════════════════════════════════════════════════════════════════════
def exposant_invariance_zero_enonce(a="Aexi0"):
    """L'ÉNONCÉ (formule) du pont à l'exposant 0 :

        Card(𝓕(0; a)) = Card(𝓕(∅; a)),     i.e.  a^0 = Card(𝓕(∅; a)).

    0 := ZERO = Card(∅).  Même nature que (B) : a^0 = Card(𝓕(ZERO;a)) avec ZERO=Card∅
    ≠ ∅ littéral, donc (B0) = exponent-invariance à l'exposant 0 — instance de
    `eq_exposant_invariant` en X=ZERO, Y=∅ (Eq(Card∅,∅)).  Composé à
    `exposant_zero_egale_un` (Card(𝓕(∅;a))=Card({∅})=1, CLOS) il donne a^0=1=Fini."""
    va = _t(a)
    lhs = exposant_cardinal_binaire(va, ZERO)        # a^0 = Card(𝓕(0;a))
    rhs = cardinal(E.applications(E.VIDE, va))        # Card(𝓕(∅;a))
    return egal(lhs, rhs)


def _puissance_P(a):
    va = _t(a)
    return lambda b: est_fini(exposant_cardinal_binaire(va, _t(b)))


def _preuve_P0_puissance(a, hfa, hB0):
    """{ Fini a [hfa], B0 [hB0] } ⊢ Fini(a^0).

    a^0 =[B0] Card(𝓕(∅;a)) =[exposant_zero_egale_un] Card({∅}) = 1 ; Fini(1)."""
    from bourbaki.cardinaux.arithmetique.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
        exposant_zero_egale_un,
    )
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import fini_un, un_egale_card_singleton
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN
    va = _t(a)
    a0 = exposant_cardinal_binaire(va, ZERO)          # a^0
    eqz = exposant_zero_egale_un(va)                  # Card(𝓕(∅;a)) = Card({∅})
    # a^0 = Card(𝓕(∅;a)) = Card({∅})
    a0_eq_un = composer_egalites(hB0, eqz)            # a^0 = Card({∅})
    un = E.singleton(E.VIDE)
    card_un = cardinal(un)                             # Card({∅}) = 1
    # Fini(1) avec 1 = UN = successeur(0) ; on transporte Fini(UN) → Fini(Card({∅}))
    # via un_egale_card_singleton : UN = Card({∅}).
    fini_UN = fini_un()                               # Fini(UN)
    assert fini_UN.conclusion == est_fini(UN), "fini_un : forme inattendue"
    un_eq = un_egale_card_singleton()                 # UN = Card({∅})
    leib_un = N.s6(UN, card_un, "wfiniun", est_fini(var("wfiniun")))  # (UN=Card{∅})⇒(Fini UN⇔Fini Card{∅})
    fini_1 = N.modus_ponens(fini_UN, equivalence_avant(N.modus_ponens(un_eq, leib_un)))  # Fini(Card({∅}))
    assert fini_1.conclusion == est_fini(card_un), "Fini(Card{∅}) : forme inattendue"
    # Leibniz : a^0 = Card({∅}) ⇒ (Fini(a^0) ⇔ Fini(Card{∅}))
    leib = N.s6(a0, card_un, "wp0pu", est_fini(var("wp0pu")))
    eqv = N.modus_ponens(a0_eq_un, leib)
    return N.modus_ponens(fini_1, equivalence_arriere(eqv))   # Fini(a^0)


def _preuve_step_puissance(a, hfa, hBuniv, n="npu"):
    """{ Fini a [hfa], (∀m)B [hBuniv] } ⊢ (∀n)( (Fini n et Fini(a^n)) ⇒ Fini(a^(n+1)) )."""
    from bourbaki.logique.i_1_termes_relations.formule import pourtout
    va = _t(a)
    vn = var(n)
    ca = conjonction_elim_gauche(hfa)                 # est_cardinal a
    pow_an = exposant_cardinal_binaire(va, vn)        # a^n
    prod_an_a = produit_cardinal_binaire(pow_an, va)  # a^n · a
    hstep = N.assume(et(est_fini(vn), est_fini(pow_an)))
    fini_n = conjonction_elim_gauche(hstep)           # Fini n
    fini_an = conjonction_elim_droite(hstep)          # Fini(a^n)
    cn = conjonction_elim_gauche(fini_n)              # est_cardinal n
    # (B) à l'instance n :  Card(𝓕(n+1;a)) = Card(𝓕(n⊔{∅};a))
    Bn = instancie(hBuniv, vn)                        # exposant_invariance_enonce(a, n)
    # maillon : B(n) ⇒ ((card a et card n) ⇒ a^(n+1)=a^n·a)
    mse = puissance_succ_eq(va, vn)
    a_n1_eq = N.modus_ponens(conjonction_intro(ca, cn),
                             N.modus_ponens(Bn, mse))  # a^(n+1) = a^n·a
    # Fini(a^n) et Fini a ⇒ Fini(a^n · a)   (G1 = produit_binaire_entier, REUTILISÉ)
    pbe = _produit_binaire_entier_t(pow_an, va)       # (Fini(a^n) et Fini a)⇒Fini(a^n·a)
    fini_prod = N.modus_ponens(conjonction_intro(fini_an, hfa), pbe)  # Fini(a^n·a)
    # Leibniz : a^(n+1)=a^n·a ⇒ (Fini(a^(n+1)) ⇔ Fini(a^n·a))
    lhs = exposant_cardinal_binaire(va, successeur(vn))   # a^(n+1)
    leib = N.s6(lhs, prod_an_a, "wpstpu", est_fini(var("wpstpu")))
    eqv = N.modus_ponens(a_n1_eq, leib)
    fini_a_n1 = N.modus_ponens(fini_prod, equivalence_arriere(eqv))   # Fini(a^(n+1))
    body = N.loi_deduction(et(est_fini(vn), est_fini(pow_an)), fini_a_n1)
    return N.generalisation(n, body)


def _produit_binaire_entier_t(x, y):
    """produit_binaire_entier version TERME capture-safe."""
    gen = N.generalisation("xpbet", N.generalisation("ypbet",
            produit_binaire_entier("xpbet", "ypbet")))
    return instancie(instancie(gen, _t(x)), _t(y))


def puissance_entiers_ferme(a="apuf", b="bpuf", n="npuf", k="kpuf"):
    """🎯 G2 — ⊢ ( B0(a) et (∀m) B(a,m) ) ⇒ ( (Fini a et Fini b) ⇒ Fini(a^b) ).

    PROPOSITION (Cor. 3, §III.5.1) : la PUISSANCE de deux entiers est un entier,
    CERTIFIÉE sous les SEULES hypothèses de support (B0)+(B) (exponent-invariance,
    non circulaires).  Récurrence C61 sur b avec P[b]:=Fini(a^b) :
        • P[0]   : a^0=1 fini           [_preuve_P0_puissance, sous B0] ;
        • P[n]⇒P[n+1] : a^(n+1)=a^n·a    [puissance_succ_eq, sous B(n)] ; Fini par G1.
    theorie=22.  La décharge de (B0)+(B) = keystone `eq_exposant_invariant` (REPORTÉ).
    """
    from bourbaki.logique.i_1_termes_relations.formule import pourtout
    va, vb = _t(a), _t(b)
    P = _puissance_P(va)

    B0_form = exposant_invariance_zero_enonce(va)
    Buniv_form = pourtout("mPpu", exposant_invariance_enonce(va, "mPpu"))

    hfa = N.assume(est_fini(va))
    hB0 = N.assume(B0_form)
    hBuniv = N.assume(Buniv_form)

    p0 = _preuve_P0_puissance(va, hfa, hB0)            # Fini(a^0)   [Fini a, B0]
    step = _preuve_step_puissance(va, hfa, hBuniv, n)  # (∀n)(...)   [Fini a, (∀m)B]
    assert p0.conclusion == P(ZERO), "P[0] puissance mal formé"
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import _fini_et_P_implique_succ
    assert step.conclusion == _fini_et_P_implique_succ(P, n), "pas puissance mal formé"

    princ_imp = principe_recurrence_preuve(P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "predecesseur_fini_universel absent"
    princ_imp = _cut(princ_imp, pfu, predecesseur_fini_universel_preuve(k=k))

    ante = conjonction_intro(p0, step)
    fini_implique_Pb = N.modus_ponens(ante, princ_imp)   # (∀b)(Fini b ⇒ Fini(a^b))  [Fini a,B0,(∀m)B]

    hconj = N.assume(et(est_fini(va), est_fini(vb)))
    fa = conjonction_elim_gauche(hconj)
    fb = conjonction_elim_droite(hconj)
    fini_impl_Pb_2 = _cut(fini_implique_Pb, est_fini(va), fa)
    Pb2 = N.modus_ponens(fb, instancie(fini_impl_Pb_2, vb))    # Fini(a^b)  [B0,(∀m)B,Fini a et Fini b]
    sous_finis = N.loi_deduction(et(est_fini(va), est_fini(vb)), Pb2)
    # décharge B0 puis (∀m)B  (et Fini a déjà absorbé via fa)
    out_B = N.loi_deduction(Buniv_form, sous_finis)
    out = N.loi_deduction(B0_form, out_B)
    cible = impl(B0_form, impl(Buniv_form,
                impl(et(est_fini(va), est_fini(vb)),
                     est_fini(exposant_cardinal_binaire(va, vb)))))
    assert out.conclusion == cible, "puissance_entiers_ferme : conclusion inattendue"
    return out


__all__ = ["exposant_invariance_enonce", "exposant_invariance_zero_enonce",
           "puissance_succ_eq", "puissance_entiers_ferme"]
