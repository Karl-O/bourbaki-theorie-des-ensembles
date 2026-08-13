"""§III.4.1 — « 2 EST UN ENTIER NATUREL » :  ⊢ Fini(2).  Troisième entier concret.

Suite des jalons Fini(0) (ensembles_fini_zero) et Fini(1) (ensembles_fini_un).  Le
verrou de Fini(2) = « 2 ≠ 2+1 » (c.-à-d. 2 ≠ 3) ÉTAIT reporté : il ne se ramène pas
au pigeonhole « image d'un singleton » (le domaine n'est plus un singleton) — il
exigeait la PROPOSITION 8 (injectivité du successeur cardinal 𝔞+1=𝔟+1 ⇒ 𝔞=𝔟).

La Proposition 8 est désormais ENTIÈRE (ensembles_prop8_fini2.prop8_successeur_injectif,
CAS 2 fermé par la transposition CONSTRUITE).  On en déduit Fini(2) :

  • _card_idempotent_t(X)   — ⊢ Card(Card X) = Card X   (un cardinal est son propre
        cardinal ; Eq(X,Card X) [equipotent_son_cardinal] + Prop. 1 sens direct) ;
  • card_un_egale_un        — ⊢ Card(1) = 1   (idempotence sur {∅}, réécrit 1=Card{∅}) ;
  • card_deux_egale_deux    — ⊢ Card(2) = 2   (idempotence sur 1⊔{∅} ; 2 = Card(1⊔{∅})) ;
  • deux_distinct_successeur_deux — ⊢ ¬(2 = 2+1)  :  Prop. 8 à (A=1, B=2) donne
        (succ 1 = succ 2) ⇒ (Card 1 = Card 2) ; or ¬(1 = 2) (un_distinct_successeur_un,
        car 2 = succ 1) et Card 1 = 1, Card 2 = 2, donc ¬(Card 1 = Card 2) ; la
        CONTRAPOSÉE donne ¬(succ 1 = succ 2) = ¬(2 = succ 2) = ¬(2 = 2+1) ;
  • deux_est_un_cardinal    — ⊢ 2 est un cardinal  (2 = Card(1⊔{∅}), card_est_un_cardinal) ;
  • fini_deux               — ⊢ Fini(2) = (2 cardinal) ∧ (2 ≠ 2+1)  =  2 EST UN ENTIER
        NATUREL  (E.III.4.1, Déf. 1).  LE JALON.

Tout est CERTIFIÉ par le noyau (aucun axiome nouveau, aucun postulat — la transposition
qui ferme la Prop. 8 est un terme CONSTRUIT, ses 4 conjoints de bijection prouvés).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, non, et
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal, est_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (equipotent_son_cardinal,
                                          cardinal_egal_si_equipotent)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (instancie, contraposition)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (symetrie,
                                          composer_egalites, congruence_terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import UN, DEUX, successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import card_est_un_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (un_distinct_successeur_un,
                                                un_egale_card_singleton)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.ensembles_prop8_fini2 import (
    prop8_successeur_injectif)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe


_SING = E.singleton(E.VIDE)                  # {∅}  (= 1 comme marqueur)
_UNSOMME = somme_disjointe(UN, _SING)        # 1 ⊔ {∅}  ;  DEUX = Card(1 ⊔ {∅})


def _card_idempotent_t(tX):
    """⊢ Card(Card X) = Card X   pour un TERME X.   (un cardinal est son propre cardinal.)

    Eq(X, Card X) (equipotent_son_cardinal) ; la Proposition 1 sens direct
    (cardinal_egal_si_equipotent à (X, Card X)) donne Card X = Card(Card X) ; symétrie."""
    eq_thm = N.generalisation("X", equipotent_son_cardinal("X"))                 # (∀X) Eq(X, Card X)
    ceq = N.generalisation("X", N.generalisation("Y",
        cardinal_egal_si_equipotent("X", "Y")))                                  # (∀X)(∀Y)(Eq(X,Y)⇒CardX=CardY)
    cX = cardinal(tX)
    eqX = instancie(eq_thm, tX)                                                  # Eq(X, Card X)
    cimp = instancie(instancie(ceq, tX), cX)                                     # Eq(X,CardX) ⇒ CardX=Card(CardX)
    cardX_eq = N.modus_ponens(eqX, cimp)                                         # Card X = Card(Card X)
    return N.modus_ponens(cardX_eq, symetrie(cX, cardinal(cX)))                  # Card(Card X) = Card X


def card_un_egale_un():
    """⊢ Card(1) = 1.   (1 est un cardinal, donc son propre cardinal.)

    Idempotence sur {∅} : Card(Card{∅}) = Card{∅} ; on réécrit Card{∅} → 1 (via
    1 = Card{∅}, un_egale_card_singleton) des deux côtés."""
    idem_sing = _card_idempotent_t(_SING)                          # Card(Card{∅}) = Card{∅}
    un_eq = un_egale_card_singleton()                              # 1 = Card({∅})
    CS = cardinal(_SING)                                           # Card({∅})
    CS_eq_un = N.modus_ponens(un_eq, symetrie(UN, CS))            # Card({∅}) = 1
    # Card({∅}) = 1  ⇒  Card(Card{∅}) = Card(1)   (Leibniz, congruence du terme Card(·))
    cong = N.modus_ponens(CS_eq_un, congruence_terme(CS, UN, cardinal(var("w"))))   # Card(Card{∅})=Card(1)
    card_un_eq_ccs = N.modus_ponens(cong, symetrie(cardinal(CS), cardinal(UN)))    # Card(1)=Card(Card{∅})
    card_un_eq_cs = composer_egalites(card_un_eq_ccs, idem_sing)                   # Card(1)=Card({∅})
    return composer_egalites(card_un_eq_cs, CS_eq_un)                             # Card(1)=1


def card_deux_egale_deux():
    """⊢ Card(2) = 2.   (2 est un cardinal, donc son propre cardinal.)

    Idempotence sur 1⊔{∅} : Card(Card(1⊔{∅})) = Card(1⊔{∅}) ; or 2 = Card(1⊔{∅})
    (définition du successeur, 2 = successeur(1)), donc le terme EST déjà Card(2)=2."""
    return _card_idempotent_t(_UNSOMME)                            # Card(Card(1⊔{∅}))=Card(1⊔{∅})  =  Card(2)=2


def deux_distinct_successeur_deux():
    """⊢ ¬(2 = 2 + 1).   (« 2 ≠ 2+1 » : 2 ≠ 3, par injectivité du successeur — Prop. 8.)

    Prop. 8 à (A=1, B=2) : (succ 1 = succ 2) ⇒ (Card 1 = Card 2).  Or ¬(1 = 2)
    (un_distinct_successeur_un : ¬(1 = succ 1) et 2 = succ 1) ; avec Card 1 = 1 et
    Card 2 = 2, ¬(Card 1 = Card 2).  La CONTRAPOSÉE de Prop. 8 donne ¬(succ 1 = succ 2)
    = ¬(2 = succ 2) = ¬(2 = 2+1)  (car succ 1 = 2 = 2+1)."""
    # Prop. 8 à (1, 2)  (par généralisation-instanciation aux termes)
    gen = N.generalisation("A", N.generalisation("B", prop8_successeur_injectif("A", "B")))
    p8 = instancie(instancie(gen, UN), DEUX)             # (succ 1 = succ 2) ⇒ (Card 1 = Card 2)

    card_un = card_un_egale_un()                          # Card(1) = 1
    card_deux = card_deux_egale_deux()                    # Card(2) = 2
    udsu = un_distinct_successeur_un()                    # ¬(1 = succ 1) = ¬(1 = 2)  (succ 1 = 2)

    # ¬(Card 1 = Card 2) : assume Card 1 = Card 2 ; 1 = Card 1 = Card 2 = 2 ; contredit ¬(1=2)
    cible_eq = egal(cardinal(UN), cardinal(DEUX))
    h = N.assume(cible_eq)
    un_eq_cun = N.modus_ponens(card_un, symetrie(cardinal(UN), UN))   # 1 = Card 1
    chain = composer_egalites(composer_egalites(un_eq_cun, h), card_deux)   # 1 = 2
    falso = N.modus_ponens(chain, N.modus_ponens(udsu,
        N.s2(non(egal(UN, DEUX)), non(cible_eq))))
    ne_card = N.modus_ponens(N.loi_deduction(cible_eq, falso), N.s1(non(cible_eq)))   # ¬(Card 1 = Card 2)

    # contraposée de Prop. 8 : ¬(Card 1 = Card 2) ⇒ ¬(succ 1 = succ 2)
    contra = contraposition(p8)
    return N.modus_ponens(ne_card, contra)               # ¬(succ 1 = succ 2) = ¬(2 = 2+1)


def deux_est_un_cardinal():
    """⊢ 2 est un cardinal  =  ⊢ (∃X)(2 = Card X).   (E.III.3.1, Déf. 2.)

    2 = Card(1⊔{∅}) (successeur(1)) est de la forme Card(X) (témoin X := 1⊔{∅}).
    card_est_un_cardinal(1⊔{∅}) = (∃X)(Card(1⊔{∅}) = Card X) = est_cardinal(2)."""
    return card_est_un_cardinal(_UNSOMME, "X")           # est_cardinal(2)


# @livre Ch.III §4.1 Rem.- | E III.31 L.12-13 | PDF p.134
def fini_deux():
    """⊢ Fini(2)  =  (2 est un cardinal) ∧ (2 ≠ 2 + 1).   (2 EST UN ENTIER NATUREL.)

    Déf. 1 (E.III.4.1) : Fini(𝔞) :⇔ (𝔞 cardinal) ∧ (𝔞 ≠ 𝔞+1).  Pour 𝔞 = 2, les DEUX
    conjoints sont certifiés : deux_est_un_cardinal et deux_distinct_successeur_deux
    (ce dernier via la PROPOSITION 8 désormais entière).  Leur conjonction EST Fini(2)
    = est_fini(2).  TROISIÈME ENTIER NATUREL concret, LE JALON de la tâche."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    card2 = deux_est_un_cardinal()                       # 2 est un cardinal
    ne = deux_distinct_successeur_deux()                 # 2 ≠ 2+1
    return conjonction_intro(card2, ne)                  # Fini(2) = est_fini(2)


__all__ = ["card_un_egale_un", "card_deux_egale_deux",
           "deux_distinct_successeur_deux", "deux_est_un_cardinal", "fini_deux"]
