"""§III.5.1 — PROPOSITION 1 (cas BINAIRE, PRODUIT) : le produit de DEUX entiers est un entier.

🎯 ⊢ ( Fini a et Fini b ) ⇒ Fini( a·b ).   (clôt produit_binaire_entier_cible.)

Miroir EXACT de somme_binaire_entier (ensembles_combinatoire_iii5) pour le produit :
récurrence C61 sur b avec P[b] := Fini(a·b), sous Fini a :
    • P[0] : a·0 = 0 (= Card∅, fini) — produit_cardinal_zero ;
    • P[n] ⇒ P[n+1] : a·(n+1) = a·n + a (produit_succ_distribue) ; Fini(a·n) et Fini a
      ⇒ Fini(a·n + a) (somme_binaire_entier).
C61 (principe_recurrence_preuve, résidu prédécesseur DÉCHARGÉ) donne
(∀b)(Fini b ⇒ Fini(a·b)).  theorie=22, 0 hyp.

Le MAILLON ALGÉBRIQUE  a·(n+1) = a·n + a  (produit_succ_distribue) :
    a·(n+1) = Card(a × (n⊔{∅}))               [produit_cardinal_bien_defini ; Card a=a,
                                                Card(n⊔{∅})=n+1 RÉFLEXIF (n+1:=Card(n⊔{∅}))]
            = Card((a×n) ⊔ (a×{∅}))           [distributivite_cardinale(a, n, {∅})]
            = Card(a×n) + Card(a×{∅})         [_sdc, réflexifs]
            = a·n + a                          [Card(a×n)=a·n déf ; Card(a×{∅})=Card a=a
                                                (produit_cardinal_un + Card a=a), congruence].
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_bien_defini,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_distributivite_cardinale import (
    distributivite_cardinale,
)
from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_petits import (
    produit_cardinal_un,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
    cardinal_de_cardinal, fini_implique_fini_successeur,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import _sdc, somme_binaire_entier
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)


from bourbaki.logique.i_1_termes_relations.formule import Terme


def _tt(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _card_de_card_t(tx):
    gen = N.generalisation("xpccd", cardinal_de_cardinal("xpccd"))
    return instancie(gen, _tt(tx))


def _pcbd_t(tX, tY, ta, tb):
    """produit_cardinal_bien_defini version TERME capture-safe (généralise+instancie).

    Prouve sur 4 NOMS frais puis instancie aux TERMES — contourne la capture des
    liants internes (pr₁/pr₂, q) quand X ou Y est une somme disjointe imbriquée."""
    g = produit_cardinal_bien_defini("Xpcbd", "Ypcbd", "apcbd", "bpcbd")
    gen = N.generalisation("Xpcbd", N.generalisation("Ypcbd",
          N.generalisation("apcbd", N.generalisation("bpcbd", g))))
    return instancie(instancie(instancie(instancie(gen, _tt(tX)), _tt(tY)), _tt(ta)), _tt(tb))


# ══════════════════════════════════════════════════════════════════════════════
#  MAILLON ALGÉBRIQUE — a·(n+1) = a·n + a   (sous a, n cardinaux)
# ══════════════════════════════════════════════════════════════════════════════
def produit_succ_distribue(a="Apsd", n="Npsd"):
    """⊢ (est_cardinal a et est_cardinal n) ⇒ a·(n+1) = a·n + a.   (Cor. Prop. 5 §III.3.3.)"""
    va, vn = _tt(a), _tt(n)
    sing = E.singleton(E.VIDE)                       # {∅}
    n_sing = somme_disjointe(vn, sing)               # n ⊔ {∅}
    succ_n = successeur(vn)                           # n+1 = Card(n⊔{∅})  (déf)
    an = produit_cardinal_binaire(va, vn)            # a·n = Card(a×n)
    a_sing = E.produit(va, sing)                      # a×{∅}
    a_n = E.produit(va, vn)                            # a×n

    h = N.assume(et(est_cardinal(va), est_cardinal(vn)))
    ca = conjonction_elim_gauche(h)
    cn = conjonction_elim_droite(h)
    card_a = N.modus_ponens(ca, _card_de_card_t(va))           # Card a = a

    # ── (A)  a·(n+1) = Card(a × (n⊔{∅})) ───────────────────────────────────────
    #   produit_cardinal_bien_defini(a, n⊔{∅}, a, n+1) :
    #     (Card a=a et Card(n⊔{∅})=n+1) ⇒ Card(a×(n⊔{∅})) = a·(n+1)
    #   Card(n⊔{∅}) = n+1 est RÉFLEXIF (n+1 := Card(n⊔{∅})).
    refl_succ = N.reflexivite(succ_n)                          # Card(n⊔{∅}) = n+1
    bd = _pcbd_t(va, n_sing, va, succ_n)
    Card_a_nsing = cardinal(E.produit(va, n_sing))
    lhs = produit_cardinal_binaire(va, succ_n)                # a·(n+1)
    eqA = N.modus_ponens(conjonction_intro(card_a, refl_succ), bd)  # Card(a×(n⊔{∅})) = a·(n+1)
    lhs_eq_card = N.modus_ponens(eqA, symetrie(Card_a_nsing, lhs))  # a·(n+1) = Card(a×(n⊔{∅}))

    # ── (B)  Card(a×(n⊔{∅})) = Card((a×n) ⊔ (a×{∅})) ──────────────────────────
    dist = distributivite_cardinale(va, vn, sing)             # Card(a×(n⊔{∅})) = Card((a×n)⊔(a×{∅}))

    # ── (C)  Card((a×n)⊔(a×{∅})) = Card(a×n) + Card(a×{∅}) ────────────────────
    refl_an = N.reflexivite(cardinal(a_n))
    refl_asing = N.reflexivite(cardinal(a_sing))
    sdc = _sdc(a_n, a_sing, cardinal(a_n), cardinal(a_sing))
    Card_union = cardinal(somme_disjointe(a_n, a_sing))
    eqC = N.modus_ponens(conjonction_intro(refl_an, refl_asing), sdc)  # = Card(a×n)+Card(a×{∅})

    # ── (D)  Card(a×n)+Card(a×{∅}) = a·n + a ──────────────────────────────────
    #   Card(a×n) == a·n syntaxiquement (déf produit_cardinal_binaire).
    #   Card(a×{∅}) = Card a = a  : produit_cardinal_un puis Card a=a, congruence sur le 2e arg.
    pu = produit_cardinal_un(va)                              # Card(a×{∅}) = Card a
    casing_eq_a = composer_egalites(pu, card_a)               # Card(a×{∅}) = a
    V = somme_cardinale_binaire(an, var("wpsd"))              # a·n + w
    eqD = N.modus_ponens(casing_eq_a,
                         congruence_terme(cardinal(a_sing), va, V, w="wpsd"))  # a·n+Card(a×{∅}) = a·n+a

    # ── ASSEMBLAGE : a·(n+1) = Card(a×(n⊔{∅})) = Card(union) = a·n+Card(a×{∅}) = a·n+a
    chain1 = composer_egalites(lhs_eq_card, dist)             # a·(n+1) = Card((a×n)⊔(a×{∅}))
    chain2 = composer_egalites(chain1, eqC)                   # a·(n+1) = Card(a×n)+Card(a×{∅})
    final = composer_egalites(chain2, eqD)                    # a·(n+1) = a·n + a
    out = N.loi_deduction(et(est_cardinal(va), est_cardinal(vn)), final)
    cible = impl(et(est_cardinal(va), est_cardinal(vn)),
                 egal(lhs, somme_cardinale_binaire(an, va)))
    assert out.conclusion == cible, "produit_succ_distribue : conclusion inattendue"
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  RÉCURRENCE — P[b] := Fini(a·b)
# ══════════════════════════════════════════════════════════════════════════════
def _P_produit(a):
    va = _tt(a)
    return lambda b: est_fini(produit_cardinal_binaire(va, _tt(b)))


def _preuve_P0_produit(a, hfa):
    """{ Fini a [hfa] } ⊢ Fini(a·0).   (a·0 = Card(a×∅) = Card∅ = 0 ; 0 fini.)"""
    va = _tt(a)
    from bourbaki.cardinaux.arithmetique.iii_3_3_produit.ensembles_produit_petits import produit_cardinal_zero
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import fini_zero
    # a·0 := produit_cardinal_binaire(a, 0) = Card(a×0).  Or 0 = ZERO = Card∅.
    #   produit_cardinal_zero(a) : Card(a×∅) = Card∅.  Mais a·0 = Card(a×ZERO) = Card(a×Card∅).
    #   ⚠ a×ZERO = a×Card∅ ≠ a×∅ littéralement.  On passe par bien_defini :
    #   produit_cardinal_bien_defini(a, ∅, a, 0) : (Card a=a et Card∅=0) ⇒ Card(a×∅)=a·0.
    ca = conjonction_elim_gauche(hfa)                          # est_cardinal a
    card_a = N.modus_ponens(ca, _card_de_card_t(va))           # Card a = a
    refl_card_vide = N.reflexivite(cardinal(E.VIDE))           # Card∅ = Card∅ = 0 (ZERO==Card∅)
    bd = _pcbd_t(va, E.VIDE, va, ZERO)    # (Card a=a et Card∅=0)⇒Card(a×∅)=a·0
    a0 = produit_cardinal_binaire(va, ZERO)                    # a·0
    Card_a_vide = cardinal(E.produit(va, E.VIDE))
    eq_a0 = N.modus_ponens(conjonction_intro(card_a, refl_card_vide), bd)  # Card(a×∅) = a·0
    # Card(a×∅) = Card∅  (produit_cardinal_zero, version TERME capture-safe)
    czero_gen = N.generalisation("Apcz", produit_cardinal_zero("Apcz"))
    czero = instancie(czero_gen, va)                           # Card(a×∅) = Card∅
    # a·0 = Card(a×∅) = Card∅ = ZERO
    a0_eq_cardvide = composer_egalites(N.modus_ponens(eq_a0, symetrie(Card_a_vide, a0)), czero)  # a·0 = Card∅ = ZERO
    # Fini(ZERO) = Fini(Card∅) ; zero_est_fini : Fini(0)
    fini_z = fini_zero()                                       # Fini(0) = Fini(Card∅)
    # Leibniz : a·0 = ZERO ⇒ (Fini(ZERO) ⇔ Fini(a·0))
    leib = N.s6(a0, ZERO, "wpp0", est_fini(var("wpp0")))       # (a·0=0)⇒(Fini(a·0)⇔Fini 0)
    eqv = N.modus_ponens(a0_eq_cardvide, leib)
    return N.modus_ponens(fini_z, equivalence_arriere(eqv))  # Fini(a·0)


def _preuve_step_produit(a, hfa, n="npro"):
    """{ Fini a [hfa] } ⊢ (∀n)( (Fini n et Fini(a·n)) ⇒ Fini(a·(n+1)) )."""
    va = _tt(a)
    vn = var(n)
    ca = conjonction_elim_gauche(hfa)                          # est_cardinal a
    prod_an = produit_cardinal_binaire(va, vn)                 # a·n
    sum_an_a = somme_cardinale_binaire(prod_an, va)            # a·n + a
    hstep = N.assume(et(est_fini(vn), est_fini(prod_an)))
    fini_n = conjonction_elim_gauche(hstep)                    # Fini n
    fini_an = conjonction_elim_droite(hstep)                   # Fini(a·n)
    cn = conjonction_elim_gauche(fini_n)                       # est_cardinal n
    # a·(n+1) = a·n + a   (produit_succ_distribue, sous card a et card n)
    psd = produit_succ_distribue(va, vn)                       # (card a et card n) ⇒ a·(n+1)=a·n+a
    a_n1_eq = N.modus_ponens(conjonction_intro(ca, cn), psd)   # a·(n+1) = a·n + a
    # Fini(a·n) et Fini a ⇒ Fini(a·n + a)  (somme_binaire_entier(a·n, a))
    sbe = _somme_binaire_entier_t(prod_an, va)                 # (Fini(a·n) et Fini a)⇒Fini(a·n+a)
    fini_sum = N.modus_ponens(conjonction_intro(fini_an, hfa), sbe)  # Fini(a·n+a)
    # Leibniz : a·(n+1) = a·n+a ⇒ (Fini(a·(n+1)) ⇔ Fini(a·n+a))
    lhs = produit_cardinal_binaire(va, successeur(vn))         # a·(n+1)
    leib = N.s6(lhs, sum_an_a, "wpstp", est_fini(var("wpstp")))
    eqv = N.modus_ponens(a_n1_eq, leib)
    fini_a_n1 = N.modus_ponens(fini_sum, equivalence_arriere(eqv))   # Fini(a·(n+1))
    body = N.loi_deduction(et(est_fini(vn), est_fini(prod_an)), fini_a_n1)
    return N.generalisation(n, body)


def _somme_binaire_entier_t(x, y):
    gen = N.generalisation("xpsbe", N.generalisation("ypsbe",
            somme_binaire_entier("xpsbe", "ypsbe")))
    return instancie(instancie(gen, _tt(x)), _tt(y))


def produit_binaire_entier(a="apbe", b="bpbe", n="npbe", k="kpbe"):
    """🎯 ⊢ (Fini a et Fini b) ⇒ Fini(produit_cardinal_binaire(a, b)).

    PROPOSITION 1 §III.5.1, cas BINAIRE PRODUIT (clôt produit_binaire_entier_cible).
    theorie=22, 0 hyp."""
    va, vb = _tt(a), _tt(b)
    P = _P_produit(va)

    hfa = N.assume(est_fini(va))
    p0 = _preuve_P0_produit(va, hfa)                           # Fini(a·0)         [Fini a]
    step = _preuve_step_produit(va, hfa, n)                    # (∀n)(...)         [Fini a]
    assert p0.conclusion == P(ZERO), "P[0] produit mal formé"
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import _fini_et_P_implique_succ
    assert step.conclusion == _fini_et_P_implique_succ(P, n), "pas produit mal formé"

    princ_imp = principe_recurrence_preuve(P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "predecesseur_fini_universel absent"
    princ_imp = _cut(princ_imp, pfu, predecesseur_fini_universel_preuve(k=k))

    ante = conjonction_intro(p0, step)
    fini_implique_Pb = N.modus_ponens(ante, princ_imp)        # (∀b)(Fini b ⇒ Fini(a·b))  [Fini a]

    hconj = N.assume(et(est_fini(va), est_fini(vb)))
    fa = conjonction_elim_gauche(hconj)
    fb = conjonction_elim_droite(hconj)
    fini_impl_Pb_2 = _cut(fini_implique_Pb, est_fini(va), fa)
    Pb2 = N.modus_ponens(fb, instancie(fini_impl_Pb_2, vb))
    res = N.loi_deduction(et(est_fini(va), est_fini(vb)), Pb2)
    cible = impl(et(est_fini(va), est_fini(vb)), est_fini(produit_cardinal_binaire(va, vb)))
    assert res.conclusion == cible, "produit_binaire_entier : conclusion inattendue"
    return res


__all__ = ["produit_succ_distribue", "produit_binaire_entier"]
