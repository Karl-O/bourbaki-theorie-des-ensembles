"""§III.5 — CALCUL SUR LES ENTIERS, 1ère vague COMBINATOIRE (E.III.34–38).

Module NEUF.  On y ferme, à partir de l'infra existante :

  • PROPOSITION 1 §III.5.1 (cas BINAIRE) — « la somme et le produit de DEUX entiers
    sont des entiers » :
        somme_binaire_entier(a,b)   ⊢ (Fini a et Fini b) ⇒ Fini(a + b)
        produit_binaire_entier(a,b) ⊢ (Fini a et Fini b) ⇒ Fini(a · b)
    (clôt les CIBLES somme_binaire_entier_cible / produit_binaire_entier_cible de
    ensembles_calcul_entiers_props), via la RÉCURRENCE C61 sur b
    (principe_recurrence_preuve, résidu predecesseur_fini_universel DÉCHARGÉ par
    sa preuve close, Prop. 2 §III.5 — exactement le motif de recurrence_finie).

    Maillon algébrique CLOS :
        somme_succ_distribue(a,b) ⊢ (card a et card b) ⇒ a+(b+1) = (a+b)+1
    (associativité de la somme cardinale + définition fidèle du successeur).

INVARIANT : theorie_ensembles() = 22.  Rien postulé : C61 est déchargé de son unique
résidu (predecesseur) par sa preuve close ; le maillon successeur est dérivé de
l'associativité (close) et de la définition du successeur.

⚠ Bourbaki E.III.35, Prop. 1 (LU au PDF source) : « Soit (a_ι)_{ι∈I} une famille
finie d'entiers.  Les cardinaux ∑a_ι et ∏a_ι sont alors des entiers. […] Montrons
d'abord que, si a et b sont des entiers, a + b est un entier.  Procédons par
récurrence sur b. […] si a+b est entier, il en est de même de (a+b)+1 (III, p. 31,
prop. 1) ; mais (a+b)+1 = a+(b+1) (III, p. 27, corollaire), donc a+(b+1) est entier. »
C'est EXACTEMENT la preuve formalisée ici (cas binaire).
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, existe, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.entiers.ensembles_entiers import est_fini, successeur, ZERO
from bourbaki.ensembles.familles.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

# ── briques CLOSES réutilisées ──────────────────────────────────────────────────
from bourbaki.cardinaux.arithmetique.ensembles_arith_somme import (
    somme_disjointe_cardinal, somme_cardinale_associative,
)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_successeur import (
    successeur_egale_card_somme,
)
from bourbaki.entiers.ensembles_fini_successeur import (
    cardinal_de_cardinal, fini_implique_fini_successeur,
)
from bourbaki.entiers.ensembles_entiers_theoremes import fini_implique_cardinal

# C61 (récurrence sur ℕ) + décharge du résidu prédécesseur
from bourbaki.entiers.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.entiers.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _cut(thm, hyp, preuve_hyp):
    """De Γ∪{H}⊢C et Δ⊢H, déduit Γ∪Δ⊢C (décharge de H puis MP)."""
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _sdc(X, Y, a, b):
    """⊢ (Card X = a et Card Y = b) ⇒ Card(X⊔Y) = somme_cardinale_binaire(a, b),
    pour des TERMES X,Y,a,b QUELCONQUES (y compris des sommes disjointes imbriquées).

    somme_disjointe_cardinal a des liants internes « a », « b » (pr₁/pr₂) qui
    capturent quand X est lui-même une somme disjointe ; on contourne en prouvant
    sur des NOMS frais puis en instanciant aux termes (motif _prop1_direct_t)."""
    g = somme_disjointe_cardinal("Xsdc", "Ysdc", "asdc", "bsdc")
    gen = N.generalisation("Xsdc", N.generalisation("Ysdc",
          N.generalisation("asdc", N.generalisation("bsdc", g))))
    return instancie(instancie(instancie(instancie(gen, _t(X)), _t(Y)), _t(a)), _t(b))


# ════════════════════════════════════════════════════════════════════════════
#  MAILLON ALGÉBRIQUE — a + (b+1) = (a+b) + 1   (sous a, b cardinaux)
# ════════════════════════════════════════════════════════════════════════════
def somme_succ_distribue(a="Asd", b="Bsd"):
    """⊢ (est_cardinal a et est_cardinal b) ⇒
         somme_cardinale_binaire(a, successeur(b)) = successeur(somme_cardinale_binaire(a, b)).

    « a + (b+1) = (a+b) + 1 »  (Cor. de Prop. 5 §III.3.3, E.III.27).  Chaîne (TERMES) :
        a+(b+1) = Card(a ⊔ (b⊔{∅}))                 [sdc(a, b⊔{∅}, a, b+1) ; Card a=a, Card(b⊔{∅})=b+1]
                = Card((a⊔b) ⊔ {∅})                 [associativité, symétrisée]
                = somme_cardinale_binaire(a+b, Card{∅})  [sdc(a⊔b, {∅}, a+b, Card{∅}) ; Card(a⊔b)=a+b]
        (a+b)+1 = successeur(a+b) = Card((a+b) ⊔ {∅})
                = somme_cardinale_binaire(a+b, Card{∅})  [sdc(a+b, {∅}, a+b, Card{∅}) ; Card(a+b)=a+b].
    Les deux membres rejoignent somme_cardinale_binaire(a+b, Card{∅}).
    """
    va, vb = _t(a), _t(b)
    sing = E.singleton(E.VIDE)
    card_sing = cardinal(sing)                          # Card{∅}
    b_sing = somme_disjointe(vb, sing)                  # b ⊔ {∅}
    succ_b = successeur(vb)                             # b+1 = Card(b⊔{∅})  (def)
    ab = somme_disjointe(va, vb)                        # a ⊔ b
    sum_ab = somme_cardinale_binaire(va, vb)            # a+b = Card(a⊔b)    (def)

    h = N.assume(et(est_cardinal(va), est_cardinal(vb)))
    ca = conjonction_elim_gauche(h)                     # est_cardinal a
    cb = conjonction_elim_droite(h)                     # est_cardinal b

    # Card a = a   (cardinal_de_cardinal, version générale instanciée au TERME a)
    cdc_gen = N.generalisation("zcdc", cardinal_de_cardinal("zcdc"))
    card_a = N.modus_ponens(ca, instancie(cdc_gen, va))             # Card a = a

    # Card(b⊔{∅}) = b+1   (def : b+1 = Card(b⊔{∅}) ; successeur_egale_card_somme symétrisé)
    succb_def = successeur_egale_card_somme(b if isinstance(b, str) else vb)  # b+1 = Card(b⊔{∅})
    card_bsing = N.modus_ponens(succb_def, symetrie(succ_b, cardinal(b_sing)))  # Card(b⊔{∅}) = b+1

    # ── (A)  a+(b+1) = Card(a ⊔ (b⊔{∅})) ───────────────────────────────────────
    sdc_A = _sdc(va, b_sing, va, succ_b)
    # (Card a=a et Card(b⊔{∅})=b+1) ⇒ Card(a⊔(b⊔{∅})) = somme_cardinale_binaire(a, b+1)
    lhs = somme_cardinale_binaire(va, succ_b)           # a+(b+1)
    Card_a_bsing = cardinal(somme_disjointe(va, b_sing))
    eqA = N.modus_ponens(conjonction_intro(card_a, card_bsing), sdc_A)  # Card(a⊔(b⊔{∅})) = a+(b+1)
    lhs_eq_card = N.modus_ponens(eqA, symetrie(Card_a_bsing, lhs))      # a+(b+1) = Card(a⊔(b⊔{∅}))

    # ── (B)  Card(a⊔(b⊔{∅})) = Card((a⊔b)⊔{∅}) ──────────────────────────────────
    assoc = somme_cardinale_associative(va, vb, sing)   # Card((a⊔b)⊔{∅}) = Card(a⊔(b⊔{∅}))
    Card_ab_sing = cardinal(somme_disjointe(ab, sing))
    assoc_sym = N.modus_ponens(assoc, symetrie(Card_ab_sing, Card_a_bsing))  # Card(a⊔(b⊔{∅}))=Card((a⊔b)⊔{∅})

    # ── (C)  Card((a⊔b)⊔{∅}) = somme_cardinale_binaire(a+b, Card{∅}) ────────────
    # Card(a⊔b)=a+b est DÉFINITIONNEL (sum_ab := Card(a⊔b)), mais sdc exige est_cardinal-libre :
    # premisse (Card(ab)=sum_ab et Card{∅}=Card{∅}), deux réflexivités.
    sdc_C = _sdc(ab, sing, sum_ab, card_sing)
    # (Card(ab)=sum_ab et Card{∅}=Card{∅}) ⇒ Card((a⊔b)⊔{∅}) = somme_cardinale_binaire(sum_ab, Card{∅})
    refl_ab = N.reflexivite(sum_ab)                     # Card(a⊔b) = a+b  (sum_ab == Card(ab))
    refl_sing = N.reflexivite(card_sing)                # Card{∅} = Card{∅}
    rhs_target = somme_cardinale_binaire(sum_ab, card_sing)   # (a+b) + Card{∅}
    eqC = N.modus_ponens(conjonction_intro(refl_ab, refl_sing), sdc_C)  # Card((a⊔b)⊔{∅}) = rhs_target

    # ── (D)  successeur(a+b) = somme_cardinale_binaire(a+b, Card{∅}) ─────────────
    # successeur(sum_ab) = Card(sum_ab ⊔ {∅})  (def), puis sdc(sum_ab, {∅}, sum_ab, Card{∅}).
    succ_sumab = successeur(sum_ab)                     # (a+b)+1 = Card(sum_ab ⊔ {∅})  (def)
    succ_def = successeur_egale_card_somme(sum_ab)      # (a+b)+1 = Card(sum_ab ⊔ {∅})
    sumab_sing = somme_disjointe(sum_ab, sing)
    # Card(sum_ab) = a+b : sum_ab est un cardinal (Card(a⊔b)) → cardinal_de_cardinal,
    #   mais on n'a pas est_cardinal(sum_ab) en hyp.  On l'obtient : sum_ab = Card(ab) est cardinal.
    from bourbaki.entiers.ensembles_entiers_theoremes import card_est_un_cardinal
    card_sumab_is_card = card_est_un_cardinal(ab, "X")             # est_cardinal(Card(a⊔b)) = est_cardinal(sum_ab)
    card_sumab = N.modus_ponens(card_sumab_is_card, instancie(cdc_gen, sum_ab))  # Card(sum_ab) = sum_ab
    sdc_D = _sdc(sum_ab, sing, sum_ab, card_sing)
    # (Card(sum_ab)=sum_ab et Card{∅}=Card{∅}) ⇒ Card(sum_ab⊔{∅}) = somme_cardinale_binaire(sum_ab, Card{∅})
    eqD = N.modus_ponens(conjonction_intro(card_sumab, refl_sing), sdc_D)  # Card(sum_ab⊔{∅}) = rhs_target
    # successeur(a+b) = Card(sum_ab⊔{∅})  [succ_def]  → composer avec eqD
    succ_eq_rhs = composer_egalites(succ_def, eqD)      # successeur(a+b) = rhs_target

    # ── ASSEMBLAGE : a+(b+1) = Card(a⊔(b⊔{∅})) = Card((a⊔b)⊔{∅}) = rhs = successeur(a+b)
    chain1 = composer_egalites(lhs_eq_card, assoc_sym)  # a+(b+1) = Card((a⊔b)⊔{∅})
    chain2 = composer_egalites(chain1, eqC)             # a+(b+1) = rhs_target
    rhs_eq_succ = N.modus_ponens(succ_eq_rhs, symetrie(succ_sumab, rhs_target))  # rhs_target = successeur(a+b)
    final = composer_egalites(chain2, rhs_eq_succ)      # a+(b+1) = successeur(a+b)

    res = N.loi_deduction(et(est_cardinal(va), est_cardinal(vb)), final)
    cible = impl(et(est_cardinal(va), est_cardinal(vb)),
                 egal(lhs, succ_sumab))
    assert res.conclusion == cible, "somme_succ_distribue : conclusion inattendue"
    return res


__all__ = ["somme_succ_distribue"]
