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

from bourbaki.logique.formule import Terme, var, egal, et, impl
from bourbaki.logique import noyau_abrege as N
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_arriere,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire, produit_cardinal_bien_defini,
)
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_prop9_final_close import prop9_close
from bourbaki.cardinaux.arithmetique.ensembles_exposant_un._bijection import (
    exposant_un_egale,
)
from bourbaki.entiers.ensembles_entiers import est_fini, successeur, ZERO
from bourbaki.entiers.ensembles_prop3_produit_entier_iii5 import produit_binaire_entier
from bourbaki.entiers.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.entiers.ensembles_predecesseur_prop2 import (
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
    from bourbaki.entiers.ensembles_fini_successeur import cardinal_de_cardinal
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


__all__ = ["exposant_invariance_enonce", "puissance_succ_eq"]
