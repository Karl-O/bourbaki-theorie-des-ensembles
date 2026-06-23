"""§III.4.1 — « 3 ET 4 SONT DES ENTIERS NATURELS » :  ⊢ Fini(3), ⊢ Fini(4).

Suite des jalons Fini(0) (ensembles_fini_zero), Fini(1) (ensembles_fini_un) et
Fini(2) (ensembles_fini_deux).  On certifie par le noyau que les cardinaux
3 = successeur(2) = Card(2⊔{∅}) et 4 = successeur(3) = Card(3⊔{∅}) sont des ENTIERS
NATURELS au sens de Bourbaki, c.-à-d.  Fini(𝔞) :⇔ (𝔞 cardinal) ∧ (𝔞 ≠ 𝔞+1)
(E.III.4.1, Déf. 1).

Le verrou de chaque finitude est l'argument de cardinalité « 𝔞 ≠ 𝔞+1 », ici établi
par la PROPOSITION 8 (injectivité du successeur cardinal, ensembles_prop8_fini2,
CAS 2 fermé par la transposition CONSTRUITE).  La CHAÎNE est identique à
deux_distinct_successeur_deux, décalée d'un cran :

  • card_trois_egale_trois  — ⊢ Card(3) = 3   (idempotence de Card sur 2⊔{∅} ;
        3 = successeur(2) = Card(2⊔{∅}), donc le terme EST déjà Card(3)=3) ;
  • card_quatre_egale_quatre — ⊢ Card(4) = 4  (idempotence sur 3⊔{∅} ; 4 = Card(3⊔{∅})) ;
  • trois_distinct_successeur_trois — ⊢ ¬(3 = 3+1)  (« 3 ≠ 4 ») :  Prop. 8 à (A=2, B=3)
        donne (succ 2 = succ 3) ⇒ (Card 2 = Card 3) ; or ¬(2 = 3)
        (deux_distinct_successeur_deux, car 3 = succ 2) et Card 2 = 2, Card 3 = 3,
        donc ¬(Card 2 = Card 3) ; la CONTRAPOSÉE donne ¬(succ 2 = succ 3)
        = ¬(3 = succ 3) = ¬(3 = 3+1) ;
  • quatre_distinct_successeur_quatre — ⊢ ¬(4 = 4+1)  (« 4 ≠ 5 ») :  Prop. 8 à (A=3, B=4)
        donne (succ 3 = succ 4) ⇒ (Card 3 = Card 4) ; or ¬(3 = 4)
        (trois_distinct_successeur_trois, car 4 = succ 3) et Card 3 = 3, Card 4 = 4,
        donc ¬(Card 3 = Card 4) ; la CONTRAPOSÉE donne ¬(succ 3 = succ 4)
        = ¬(4 = succ 4) = ¬(4 = 4+1) ;
  • trois_est_un_cardinal / quatre_est_un_cardinal — ⊢ 3 (resp. 4) est un cardinal
        (3 = Card(2⊔{∅}), 4 = Card(3⊔{∅}), de la forme Card X, card_est_un_cardinal) ;
  • fini_trois  — ⊢ Fini(3) = (3 cardinal) ∧ (3 ≠ 3+1)  =  3 EST UN ENTIER NATUREL ;
  • fini_quatre — ⊢ Fini(4) = (4 cardinal) ∧ (4 ≠ 4+1)  =  4 EST UN ENTIER NATUREL.

⚠ 3 et 4 sont des τ-cardinaux profondément imbriqués (3 = Card(Card(1⊔{∅})⊔{∅}) …).
Toutes les preuves restent SYMBOLIQUES : on manipule successeur(2), successeur(3) via
prop8_successeur_injectif et les ≠ déjà établis, on NE DÉPLIE JAMAIS Card.  La seule
brique qui « calcule » est l'idempotence Card(Card X)=Card X (equipotent_son_cardinal +
Prop. 1), instanciée aux termes 2⊔{∅} et 3⊔{∅} — exactement comme card_deux_egale_deux.

Tout est CERTIFIÉ par le noyau (aucun axiome nouveau, aucun postulat — la transposition
qui ferme la Prop. 8 est un terme CONSTRUIT, ses conjoints de bijection prouvés) et
TESTÉ (test_fini_trois_quatre.py).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, non
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_cardinal
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, contraposition,
                                                          conjonction_intro)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (symetrie,
                                                                 composer_egalites)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import DEUX, TROIS, QUATRE, successeur
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_deux import (_card_idempotent_t,
                                                  card_deux_egale_deux,
                                                  deux_distinct_successeur_deux)
from bourbaki.cardinaux.arithmetique.iii_3_4_prop8_successeur.ensembles_prop8_fini2 import (
    prop8_successeur_injectif)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe


_SING = E.singleton(E.VIDE)                  # {∅}  (= 1 comme marqueur)
_DEUXSOMME = somme_disjointe(DEUX, _SING)    # 2 ⊔ {∅}  ;  TROIS = Card(2 ⊔ {∅}) = succ(2)
_TROISSOMME = somme_disjointe(TROIS, _SING)  # 3 ⊔ {∅}  ;  QUATRE = Card(3 ⊔ {∅}) = succ(3)


# ═══════════════════════════════════════════════════════════════════════════════
# Card(3) = 3   et   Card(4) = 4   (idempotence du cardinal)
# ═══════════════════════════════════════════════════════════════════════════════
def card_trois_egale_trois():
    """⊢ Card(3) = 3.   (3 est un cardinal, donc son propre cardinal.)

    Idempotence sur 2⊔{∅} : Card(Card(2⊔{∅})) = Card(2⊔{∅}) ; or 3 = Card(2⊔{∅})
    (définition du successeur, 3 = successeur(2)), donc le terme EST déjà Card(3)=3.
    Miroir EXACT de card_deux_egale_deux (décalé d'un cran)."""
    return _card_idempotent_t(_DEUXSOMME)        # Card(Card(2⊔{∅}))=Card(2⊔{∅})  =  Card(3)=3


def card_quatre_egale_quatre():
    """⊢ Card(4) = 4.   (4 est un cardinal, donc son propre cardinal.)

    Idempotence sur 3⊔{∅} : Card(Card(3⊔{∅})) = Card(3⊔{∅}) ; or 4 = Card(3⊔{∅})
    (définition du successeur, 4 = successeur(3)), donc le terme EST déjà Card(4)=4."""
    return _card_idempotent_t(_TROISSOMME)       # Card(Card(3⊔{∅}))=Card(3⊔{∅})  =  Card(4)=4


# ═══════════════════════════════════════════════════════════════════════════════
# Patron commun « 𝔞 ≠ 𝔞+1 » par la Proposition 8 (injectivité du successeur)
# ═══════════════════════════════════════════════════════════════════════════════
def _distinct_successeur(a, b, card_a, card_b, ne_ab):
    """⊢ ¬(B = B + 1)   à partir de :
        a, b        : les TERMES 𝔞, 𝔟  (avec 𝔟 = successeur(𝔞)) ;
        card_a      : ⊢ Card(𝔞) = 𝔞 ;
        card_b      : ⊢ Card(𝔟) = 𝔟 ;
        ne_ab       : ⊢ ¬(𝔞 = 𝔟)   (c.-à-d. ¬(𝔞 = 𝔞+1), car 𝔟 = succ 𝔞).

    Patron de deux_distinct_successeur_deux, paramétré :  Prop. 8 à (𝔞, 𝔟) donne
    (succ 𝔞 = succ 𝔟) ⇒ (Card 𝔞 = Card 𝔟).  De ¬(𝔞 = 𝔟), Card 𝔞 = 𝔞 et Card 𝔟 = 𝔟,
    on tire ¬(Card 𝔞 = Card 𝔟) (sinon 𝔞 = Card 𝔞 = Card 𝔟 = 𝔟, contredit ¬(𝔞=𝔟)).
    La CONTRAPOSÉE de Prop. 8 donne alors ¬(succ 𝔞 = succ 𝔟) = ¬(𝔟 = succ 𝔟) = ¬(𝔟 = 𝔟+1)
    (car succ 𝔞 = 𝔟 et succ 𝔟 = 𝔟+1)."""
    # Prop. 8 à (𝔞, 𝔟)  (par généralisation-instanciation aux termes)
    gen = N.generalisation("A", N.generalisation("B", prop8_successeur_injectif("A", "B")))
    p8 = instancie(instancie(gen, a), b)              # (succ 𝔞 = succ 𝔟) ⇒ (Card 𝔞 = Card 𝔟)

    # ¬(Card 𝔞 = Card 𝔟) : assume Card 𝔞 = Card 𝔟 ; 𝔞 = Card 𝔞 = Card 𝔟 = 𝔟 ; contredit ¬(𝔞=𝔟)
    cible_eq = egal(cardinal(a), cardinal(b))
    h = N.assume(cible_eq)
    a_eq_ca = N.modus_ponens(card_a, symetrie(cardinal(a), a))    # 𝔞 = Card 𝔞
    chain = composer_egalites(composer_egalites(a_eq_ca, h), card_b)   # 𝔞 = 𝔟
    falso = N.modus_ponens(chain, N.modus_ponens(ne_ab,
        N.s2(non(egal(a, b)), non(cible_eq))))
    ne_card = N.modus_ponens(N.loi_deduction(cible_eq, falso),
                             N.s1(non(cible_eq)))                 # ¬(Card 𝔞 = Card 𝔟)

    # contraposée de Prop. 8 : ¬(Card 𝔞 = Card 𝔟) ⇒ ¬(succ 𝔞 = succ 𝔟)
    contra = contraposition(p8)
    return N.modus_ponens(ne_card, contra)            # ¬(succ 𝔞 = succ 𝔟) = ¬(𝔟 = 𝔟+1)


def trois_distinct_successeur_trois():
    """⊢ ¬(3 = 3 + 1).   (« 3 ≠ 3+1 » : 3 ≠ 4, par injectivité du successeur — Prop. 8.)

    Prop. 8 à (A=2, B=3) : (succ 2 = succ 3) ⇒ (Card 2 = Card 3).  Or ¬(2 = 3)
    (deux_distinct_successeur_deux : ¬(2 = succ 2) et 3 = succ 2) ; avec Card 2 = 2 et
    Card 3 = 3, ¬(Card 2 = Card 3).  La CONTRAPOSÉE de Prop. 8 donne ¬(succ 2 = succ 3)
    = ¬(3 = succ 3) = ¬(3 = 3+1)  (car succ 2 = 3 = 3+1 du membre gauche, succ 3 = 4)."""
    return _distinct_successeur(DEUX, TROIS,
                                card_deux_egale_deux(),            # Card 2 = 2
                                card_trois_egale_trois(),          # Card 3 = 3
                                deux_distinct_successeur_deux())   # ¬(2 = 3)  (3 = succ 2)


def quatre_distinct_successeur_quatre():
    """⊢ ¬(4 = 4 + 1).   (« 4 ≠ 4+1 » : 4 ≠ 5, par injectivité du successeur — Prop. 8.)

    Prop. 8 à (A=3, B=4) : (succ 3 = succ 4) ⇒ (Card 3 = Card 4).  Or ¬(3 = 4)
    (trois_distinct_successeur_trois : ¬(3 = succ 3) et 4 = succ 3) ; avec Card 3 = 3 et
    Card 4 = 4, ¬(Card 3 = Card 4).  La CONTRAPOSÉE de Prop. 8 donne ¬(succ 3 = succ 4)
    = ¬(4 = succ 4) = ¬(4 = 4+1)."""
    return _distinct_successeur(TROIS, QUATRE,
                                card_trois_egale_trois(),                # Card 3 = 3
                                card_quatre_egale_quatre(),              # Card 4 = 4
                                trois_distinct_successeur_trois())       # ¬(3 = 4)  (4 = succ 3)


# ═══════════════════════════════════════════════════════════════════════════════
# « 3 est un cardinal »  et  « 4 est un cardinal »  (1er conjoint de Fini)
# ═══════════════════════════════════════════════════════════════════════════════
def trois_est_un_cardinal():
    """⊢ 3 est un cardinal  =  ⊢ (∃X)(3 = Card X).   (E.III.3.1, Déf. 2.)

    3 = Card(2⊔{∅}) (successeur(2)) est de la forme Card(X) (témoin X := 2⊔{∅}).
    card_est_un_cardinal(2⊔{∅}) = (∃X)(Card(2⊔{∅}) = Card X) = est_cardinal(3)."""
    return card_est_un_cardinal(_DEUXSOMME, "X")     # est_cardinal(3)


def quatre_est_un_cardinal():
    """⊢ 4 est un cardinal  =  ⊢ (∃X)(4 = Card X).   (E.III.3.1, Déf. 2.)

    4 = Card(3⊔{∅}) (successeur(3)) est de la forme Card(X) (témoin X := 3⊔{∅}).
    card_est_un_cardinal(3⊔{∅}) = (∃X)(Card(3⊔{∅}) = Card X) = est_cardinal(4)."""
    return card_est_un_cardinal(_TROISSOMME, "X")    # est_cardinal(4)


# ═══════════════════════════════════════════════════════════════════════════════
# « 3 EST UN ENTIER NATUREL »  et  « 4 EST UN ENTIER NATUREL »  (JALONS)
# ═══════════════════════════════════════════════════════════════════════════════
def fini_trois():
    """⊢ Fini(3)  =  (3 est un cardinal) ∧ (3 ≠ 3 + 1).   (3 EST UN ENTIER NATUREL.)

    Déf. 1 (E.III.4.1) : Fini(𝔞) :⇔ (𝔞 cardinal) ∧ (𝔞 ≠ 𝔞+1).  Pour 𝔞 = 3, les DEUX
    conjoints sont certifiés : trois_est_un_cardinal et trois_distinct_successeur_trois
    (ce dernier via la PROPOSITION 8).  Leur conjonction EST Fini(3) = est_fini(3).
    QUATRIÈME ENTIER NATUREL concret."""
    card3 = trois_est_un_cardinal()                  # 3 est un cardinal
    ne = trois_distinct_successeur_trois()           # 3 ≠ 3+1
    return conjonction_intro(card3, ne)              # Fini(3) = est_fini(3)


def fini_quatre():
    """⊢ Fini(4)  =  (4 est un cardinal) ∧ (4 ≠ 4 + 1).   (4 EST UN ENTIER NATUREL.)

    Déf. 1 (E.III.4.1) : Fini(𝔞) :⇔ (𝔞 cardinal) ∧ (𝔞 ≠ 𝔞+1).  Pour 𝔞 = 4, les DEUX
    conjoints sont certifiés : quatre_est_un_cardinal et quatre_distinct_successeur_quatre
    (ce dernier via la PROPOSITION 8).  Leur conjonction EST Fini(4) = est_fini(4).
    CINQUIÈME ENTIER NATUREL concret."""
    card4 = quatre_est_un_cardinal()                 # 4 est un cardinal
    ne = quatre_distinct_successeur_quatre()         # 4 ≠ 4+1
    return conjonction_intro(card4, ne)              # Fini(4) = est_fini(4)


__all__ = ["card_trois_egale_trois", "card_quatre_egale_quatre",
           "trois_distinct_successeur_trois", "quatre_distinct_successeur_quatre",
           "trois_est_un_cardinal", "quatre_est_un_cardinal",
           "fini_trois", "fini_quatre"]
