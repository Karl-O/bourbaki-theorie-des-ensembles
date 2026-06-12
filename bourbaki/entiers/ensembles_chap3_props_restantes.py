"""§III — PROPOSITIONS RESTANTES atteignables (Cantor au niveau CARDINAL).

Ce module SALVAGE, INCONDITIONNELLEMENT (rien postulé, theorie_ensembles()=22), les
énoncés du chapitre III qui sont ATTEIGNABLES sans la récurrence C61 / ℕ-inconditionnel,
en exploitant le THÉORÈME DE CANTOR déjà prouvé (ensembles_cantor : X < P(X) au niveau
des ENSEMBLES) et le PONT « ≤ ensembliste ⇒ ≤ cardinal » (le_ens_implique_le_card).

────────────────────────────────────────────────────────────────────────────────
CONTENU — ce qui est NOUVELLEMENT CLOS ici (GREP : non couvert ailleurs) :

  🎯 cantor_strict_cardinal(X)   ⊢ Card X < Card P(X)        (= inf_strict_card au niveau
        des CARDINAUX).  C'est EXACTEMENT le pont que ensembles_prop12_card/_bijection.py
        signalait comme REPORTÉ (« cantor_deux_exp » y lève NotImplementedError !) :
        « X < P(X) au sens des INJECTIONS de SETS ⇒ Card X < Card P(X) au sens de l'ORDRE
        des CARDINAUX ».  Bridge : (i) ≤ par le_ens_implique_le_card(inf_egal_parties) ;
        (ii) ≠ par la contraposée de la Proposition 1 réciproque (Card X = Card P(X) ⇒
        Eq(X,P(X))), réfutée par cantor_non_equipotent (¬Eq(X,P(X))).

  🎯 cantor_deux_exp(X)          ⊢ Card X < 2^Card X         (THÉORÈME 2 de Cantor restaté,
        E.III.3.6 : 2^a > a).  cantor_strict_cardinal(X) + Card P(X) = 2^Card X
        (card_parties_egale_deux_exp, Prop. 12, CLOS) réécrit par S6.  CLÔT le report
        explicite de ensembles_prop12_card/_bijection.py:cantor_deux_exp.

  🎯 aleph0_strict_continu()     ⊢ ℵ₀ < 2^ℵ₀                 (E.III.6.4, Déf. 4 : « un
        ensemble qui a la puissance du continu n'est PAS dénombrable » — le CŒUR cardinal).
        Spécialisation de cantor_deux_exp à X := N (ℵ₀ = Card N, 2^ℵ₀ = Card P(N)).

  🎯 aleph0_inf_egal_continu()   ⊢ ℵ₀ ≤ 2^ℵ₀                 (borne large : N s'injecte
        dans P(N)).

  🎯 continu_non_denombrable_card()  ⊢ ¬( 2^ℵ₀ ≤ ℵ₀ )       (E.III.6.4 : la puissance du
        continu N'EST PAS ≤ ℵ₀, donc P(N) n'est pas dénombrable au sens cardinal
        est_denombrable_card(P N) = (Card P(N) ≤ ℵ₀)).  Asymétrie de l'ordre strict
        (inf_strict_exclut_reciproque) sous est_cardinal(ℵ₀), est_cardinal(2^ℵ₀) —
        les deux étant des Card(·), prouvés par est_cardinal_de_cardinal.

  • est_cardinal_de_cardinal(X)  ⊢ est_cardinal(Card X)      (LEMME réutilisable : tout
        Card X est un cardinal — témoin X dans (∃Y)(Card X = Card Y)).

────────────────────────────────────────────────────────────────────────────────
⚠️ INVARIANT : aucun N.axiome n'ajouté à theorie_ensembles() (=22).  Aucun théorème
   reposant sur la RÉCURRENCE n'est postulé.  Les Propositions 1-5 de III.6 (parties
   d'un dénombrable, partition, 𝔉(E)≃E…) et le Théorème 2 (𝔞²=𝔞) restent REPORTÉS
   (arithmétique cardinale infinie / collectivisation de N), cf. ensembles_infinis_props.
   Ici l'INÉGALITÉ STRICTE ℵ₀ < 2^ℵ₀ est INCONDITIONNELLE (Cantor seul).

⚠️ NOTE de fidélité « ≠ » : prop1_reciproque_t(X,P(X)) et cantor_non_equipotent(X)
   produisent TOUS DEUX la forme CANONIQUE equipotent(X,P(X)) (lieur 'F'), ce qui rend
   le modus ponens contraposé STRUCTUREL (pas seulement α-équivalent) — c'est pourquoi
   on passe par prop1_reciproque_t et par generalisation/instanciation (et NON par
   equipotent_si_cardinal_egal appelé DIRECTEMENT sur des termes, qui α-renomme).
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, non
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card, inf_strict_card,
)
from bourbaki.cardinaux.ensembles_cantor import (
    cantor_non_equipotent, inf_egal_parties,
)
from bourbaki.cardinaux.arithmetique.ensembles_prop8_successeur import prop1_reciproque_t
from bourbaki.entiers.ensembles_calcul_entiers_props import le_ens_implique_le_card
from bourbaki.entiers.ensembles_finis_props import inf_strict_exclut_reciproque
from bourbaki.entiers.ensembles_infinis import NN, aleph0, puissance_continu

from bourbaki.logique.tactiques.tactiques_abrege2 import (
    contraposition, instancie, conjonction_intro,
)


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  LEMME réutilisable :  est_cardinal(Card X)   (tout Card X est un cardinal)
#
#  est_cardinal(a) = (∃Y)(a = Card Y).  Pour a = Card X, témoin Y := X : Card X = Card X
#  (réflexivité) puis S5.  Le liant ∃ de est_cardinal est « X » (≠ liant interne « Z »
#  de cardinal=τ_Z) ; pour ÉVITER LA CAPTURE de X par ce liant, on prouve le lemme
#  GÉNÉRIQUEMENT (sujet Y libre, Card Y ne contient pas le liant X) et on instancie.
# ════════════════════════════════════════════════════════════════════════════
def est_cardinal_de_cardinal(x="X"):
    """⊢ est_cardinal(Card X).   (tout cardinal Card X est un cardinal ; INCONDITIONNEL.)

    est_cardinal(Card X) = (∃Y)(Card X = Card Y) ; témoin Y := X via réflexivité
    Card X = Card X et S5.  LEMME réutilisable (gardes est_cardinal des asymétries
    cardinales sur des Card(·)).  Prouvé sans capture : le liant ∃ est « X » mais le
    SUJET passé (le terme x, ici renommable) n'est pas lié — Card x ne contient pas le
    liant.  (Pour x = Card N, Card P(N)… : appeler directement avec le TERME.)"""
    vX = _t(x)
    cX = cardinal(vX)
    R = egal(cX, cardinal(var("X")))                      # Card x = Card X  (liant ∃ : X)
    refl = N.reflexivite(cX)                              # ⊢ Card x = Card x
    return N.modus_ponens(refl, N.s5(R, vX, "X"))         # (∃X)(Card x = Card X) = est_cardinal(Card x)


# ════════════════════════════════════════════════════════════════════════════
#  (1) CANTOR au niveau CARDINAL :  Card X < Card P(X)   (INCONDITIONNEL)
#
#  Card X < Card P(X) = ( Card X ≤ Card P(X) ) et ( Card X ≠ Card P(X) ).
#    • ≤ : X ≤ P(X) (inf_egal_parties, injection x↦{x}) puis le pont
#          le_ens_implique_le_card → Card X ≤ Card P(X) ;
#    • ≠ : si Card X = Card P(X), la Prop. 1 réciproque (prop1_reciproque_t) donnerait
#          Eq(X,P(X)), réfutée par cantor_non_equipotent (argument diagonal) ; d'où
#          ¬(Card X = Card P(X)) (contraposée + modus ponens).
#  C'EST LE PONT que ensembles_prop12_card/_bijection.py:cantor_deux_exp signalait comme
#  REPORTÉ (« X<P(X) au niveau SETS ⇒ Card X < Card P(X) au niveau CARDINAUX »).
# ════════════════════════════════════════════════════════════════════════════
def cantor_strict_cardinal(x="X"):
    """⊢ Card X < Card P(X).   (THÉORÈME DE CANTOR, niveau CARDINAL ; INCONDITIONNEL.)

    Ferme le pont REPORTÉ par ensembles_prop12_card/_bijection.py (cantor_deux_exp y
    lève NotImplementedError).  Card X < Card P(X) = (Card X ≤ Card P(X)) et (Card X ≠
    Card P(X)) :
      • ≤ : inf_egal_parties (X ≤ P(X)) poussé par le_ens_implique_le_card ;
      • ≠ : contraposée de prop1_reciproque_t (Card X = Card P(X) ⇒ Eq(X,P(X))), réfutée
            par cantor_non_equipotent (¬Eq(X,P(X))).
    Les deux formes Eq(X,P(X)) (Prop. 1 réciproque et Cantor) sont CANONIQUES (lieur 'F')
    ⇒ modus ponens STRUCTUREL.  x : nom (str) OU Terme."""
    vX = _t(x)
    PX = E.parties(vX)
    # (a) Card X ≤ Card P(X)
    le_ens = inf_egal_parties(vX)                         # ⊢ X ≤ P(X)   (injection x↦{x})
    le_card = N.modus_ponens(le_ens, le_ens_implique_le_card(vX, PX))   # Card X ≤ Card P(X)
    # (b) Card X ≠ Card P(X)
    rec = prop1_reciproque_t(vX, PX)                      # (Card X = Card P(X)) ⇒ Eq(X,P(X))
    contra = contraposition(rec)                          # ¬Eq(X,P(X)) ⇒ ¬(Card X = Card P(X))
    nonEq = instancie(N.generalisation("X", cantor_non_equipotent("X")), vX)   # ¬Eq(X,P(X))
    ne_card = N.modus_ponens(nonEq, contra)               # ¬(Card X = Card P(X))
    return conjonction_intro(le_card, ne_card)            # Card X < Card P(X)


# ════════════════════════════════════════════════════════════════════════════
#  (2) THÉORÈME 2 de Cantor restaté :  Card X < 2^Card X   (INCONDITIONNEL)
#
#  Card P(X) = 2^Card X (Proposition 12, card_parties_egale_deux_exp, CLOS).  On réécrit
#  le MAJORANT Card P(X) ↦ 2^Card X dans Card X < Card P(X) (S6 sur le 2ᵉ argument).
#  CLÔT le report explicite « cantor_deux_exp » de ensembles_prop12_card.
# ════════════════════════════════════════════════════════════════════════════
def _card_parties_egale_deux_exp_t(vX):
    """⊢ Card P(X) = 2^Card X  pour un TERME X (Prop. 12 généralisée+instanciée)."""
    from bourbaki.cardinaux.arithmetique.ensembles_prop12_card import card_parties_egale_deux_exp
    gen = N.generalisation("X", card_parties_egale_deux_exp("X"))
    return instancie(gen, vX)


def cantor_deux_exp(x="X"):
    """⊢ Card X < 2^Card X.   (THÉORÈME 2 de Cantor, E.III.3.6 : 2^a > a ; INCONDITIONNEL.)

    CLÔT le report homonyme de ensembles_prop12_card/_bijection.py (qui y lève
    NotImplementedError).  cantor_strict_cardinal(X) ⊢ Card X < Card P(X) ; la
    Proposition 12 (card_parties_egale_deux_exp) ⊢ Card P(X) = 2^Card X ; on réécrit le
    majorant Card P(X) ↦ 2^Card X (S6 sur le 2ᵉ argument de inf_strict_card), via
    equivalence_avant.  2^Card X = exposant_cardinal_binaire(2, X)."""
    from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import exposant_cardinal_binaire
    from bourbaki.cardinaux.arithmetique.ensembles_powerset_exp import deux
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    vX = _t(x)
    PX = E.parties(vX)
    cX, cPX = cardinal(vX), cardinal(PX)
    strict = cantor_strict_cardinal(x)                    # Card X < Card P(X)
    eq = _card_parties_egale_deux_exp_t(vX)               # Card P(X) = 2^Card X
    deux_exp = exposant_cardinal_binaire(deux(), vX)      # 2^Card X
    # S6 : (Card P(X) = 2^Card X) ⇒ ( (Card X < Card P(X)) ⇔ (Card X < 2^Card X) )
    s6 = N.s6(cPX, deux_exp, "w", inf_strict_card(cX, var("w")))
    equ = N.modus_ponens(eq, s6)
    return N.modus_ponens(strict, equivalence_avant(equ))  # Card X < 2^Card X


# ════════════════════════════════════════════════════════════════════════════
#  (3) ℵ₀ < 2^ℵ₀  et  ℵ₀ ≤ 2^ℵ₀   (E.III.6.4, Déf. 4 — la puissance du continu)
#
#  ℵ₀ = Card N, 2^ℵ₀ = Card P(N) = puissance_continu().  Spécialisations de Cantor à N.
# ════════════════════════════════════════════════════════════════════════════
def aleph0_strict_continu():
    """⊢ ℵ₀ < 2^ℵ₀.   (E.III.6.4 : la puissance du continu DÉPASSE STRICTEMENT ℵ₀ ; INCONDITIONNEL.)

    Spécialisation de cantor_strict_cardinal à X := N : ℵ₀ = Card N, 2^ℵ₀ = Card P(N) =
    puissance_continu().  « Un ensemble qui a la puissance du continu n'est pas
    dénombrable » (Déf. 4) — cœur cardinal, INCONDITIONNEL (Cantor seul, sans récurrence
    ni arithmétique cardinale infinie)."""
    return cantor_strict_cardinal(NN)                     # Card N < Card P(N) = ℵ₀ < 2^ℵ₀


def aleph0_inf_egal_continu():
    """⊢ ℵ₀ ≤ 2^ℵ₀.   (N s'injecte dans P(N) ; borne large ; INCONDITIONNEL.)

    Conjoint gauche de aleph0_strict_continu (projection du < = ≤ et ≠).  Card N ≤
    Card P(N) = ℵ₀ ≤ 2^ℵ₀ (le pont sur l'injection x↦{x})."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_elim_gauche
    return conjonction_elim_gauche(aleph0_strict_continu())   # ℵ₀ ≤ 2^ℵ₀


# ════════════════════════════════════════════════════════════════════════════
#  (4) La puissance du continu N'EST PAS ≤ ℵ₀   (P(N) non dénombrable, sens cardinal)
#
#  ¬( 2^ℵ₀ ≤ ℵ₀ ).  Asymétrie de l'ordre strict des CARDINAUX (inf_strict_exclut_
#  reciproque) : sous est_cardinal(ℵ₀) et est_cardinal(2^ℵ₀), de ℵ₀ < 2^ℵ₀ on tire
#  ¬(2^ℵ₀ ≤ ℵ₀).  ℵ₀ = Card N et 2^ℵ₀ = Card P(N) SONT des cardinaux (est_cardinal_de_
#  cardinal).  est_denombrable_card(P N) = (Card P(N) ≤ ℵ₀) ; on en prouve la NÉGATION.
# ════════════════════════════════════════════════════════════════════════════
def continu_non_denombrable_card():
    """⊢ ¬( 2^ℵ₀ ≤ ℵ₀ ).   (E.III.6.4 : la puissance du continu n'est PAS dénombrable ; INCONDITIONNEL.)

    2^ℵ₀ = Card P(N) = puissance_continu().  est_denombrable_card(P N) = (Card P(N) ≤ ℵ₀) ;
    cet énoncé en est la NÉGATION : P(N) n'est pas dénombrable (au sens cardinal).
    Preuve : ℵ₀ < 2^ℵ₀ (aleph0_strict_continu) ; asymétrie inf_strict_exclut_reciproque
    (sous est_cardinal des deux membres : Card N, Card P(N), via est_cardinal_de_cardinal)
    donne (ℵ₀ < 2^ℵ₀) ⇒ ¬(2^ℵ₀ ≤ ℵ₀).  INCONDITIONNEL (Cantor + antisymétrie de ≤)."""
    cN = aleph0()                                         # ℵ₀ = Card N
    cPN = puissance_continu()                             # 2^ℵ₀ = Card P(N)
    strict = aleph0_strict_continu()                     # ℵ₀ < 2^ℵ₀
    asym = inf_strict_exclut_reciproque(cN, cPN)         # est_c(a)⇒(est_c(b)⇒((a<b)⇒¬(b≤a)))
    s1 = N.modus_ponens(est_cardinal_de_cardinal(NN), asym)           # est_c(b)⇒((a<b)⇒¬(b≤a))
    s2 = N.modus_ponens(est_cardinal_de_cardinal(E.parties(NN)), s1)  # (a<b)⇒¬(b≤a)
    return N.modus_ponens(strict, s2)                    # ¬( 2^ℵ₀ ≤ ℵ₀ )


__all__ = [
    # LEMME réutilisable
    "est_cardinal_de_cardinal",
    # 🎯 CANTOR au niveau CARDINAL — clôt le report cantor_deux_exp de prop12
    "cantor_strict_cardinal",
    "cantor_deux_exp",
    # 🎯 puissance du continu (Déf. 4, E.III.6.4) — INCONDITIONNELS
    "aleph0_strict_continu",
    "aleph0_inf_egal_continu",
    "continu_non_denombrable_card",
]
