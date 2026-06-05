"""§III.4.1 — « 0 EST UN ENTIER NATUREL » :  ⊢ Fini(0).  Premier entier concret.

Avec le successeur redéfini FIDÈLEMENT (ensembles_entiers.py, round 13) comme la
somme cardinale  successeur(𝔞) := 𝔞 + 1 := somme_cardinale_binaire(𝔞, {∅}) =
Card(𝔞 ⊔ {∅})  (E.III.4.1, Déf. 1 ; E.III.3.3, Déf. 3 ; 1 = Card({∅}), E.III.3.1,
Déf. 2, Exemple), on certifie par le noyau les premiers résultats de finitude :

  • cardinal_vide_egale_vide      (clos) — Card(∅) = ∅   (= « 0 = ∅ », E.III.3.1,
        Exemple 1 ; via Eq(∅, Card∅) + image_sur_vide : une bijection ∅ → Card∅ a
        pour image ∅, et la surjectivité force Card∅ = ∅) ;
  • successeur_zero_egale_un       (clos) — successeur(0) = Card({∅})  (« 0 + 1 = 1 » :
        successeur(0) = Card(Card∅ ⊔ {∅}) = Card(∅ ⊔ {∅}) [Card∅=∅] = Card({∅})
        [card_somme_zero_un]) ;
  • zero_distinct_successeur_zero   (clos) — ¬(0 = 0 + 1)  (« 0 ≠ 0+1 » : Card∅ ≠ Card{∅}
        par contraposée de la Proposition 1 sur ¬Eq(∅,{∅}), puis 1 = successeur(0)) ;
  • zero_est_un_cardinal           (clos) — 0 est un cardinal  (= card_est_un_cardinal(∅)) ;
  • fini_zero                      (clos) — Fini(0)  =  (0 est un cardinal) ∧ (0 ≠ 0+1)
        =  0 EST UN ENTIER NATUREL  (E.III.4.1, Déf. 1).  JALON : 1er entier concret.

Tout est CERTIFIÉ par le noyau (aucun axiome nouveau, aucun postulat) et TESTÉ
(test_fini_zero.py).  Les marqueurs : 0 = Card(∅) (ZERO), 1 = {∅} comme marqueur
ensembliste de la somme et Card({∅}) comme cardinal.

REPORTÉ honnêtement : Fini(1) = (1 cardinal) ∧ (1 ≠ 1+1).  Le 2e conjoint 1 ≠ 1+1
exige Card({∅}) ≠ Card({∅} ⊔ {∅}), c.-à-d. ¬Eq({∅}, {∅}⊔{∅}) (1 ≠ 2 éléments) — un
argument de cardinalité « 1 contre 2 » non encore disponible (pas de pigeonhole/
Prop. 8 𝔞+1=𝔟+1⇒𝔞=𝔟).  De plus, 1 = successeur(Card∅) est un τ-cardinal qui ne
traverse pas la machinerie de la somme (collision des liants internes du τ-cardinal,
même verrou que somme_disjointe_cardinal forme finale).  Donc Fini(1), Prop. 1
(Fini(𝔞)⇔Fini(𝔞+1)) et la récurrence C61 restent reportées.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, non, et
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import (est_bijection_de, cardinal, est_cardinal,
                                 equipotent)
from bourbaki.cardinaux.ensembles_vide_singleton import (image_sur_vide,
                                      vide_non_equipotent_singleton)
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_si_cardinal_egal
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _eq_son_cardinal_terme
from bourbaki.entiers.ensembles_zero_plus_un import card_somme_zero_un
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
from bourbaki.entiers.ensembles_entiers_theoremes import card_est_un_cardinal
from bourbaki.entiers import ensembles_entiers as Ent
from bourbaki.logique.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_droite,
                               instancie, equivalence_avant)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie, composer_egalites, congruence_terme
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination


# ── Les objets de base : 0 = Card(∅), 1 = {∅} (marqueur) / Card({∅}) (cardinal) ──
_VIDE = E.VIDE                       # ∅
_ZERO = cardinal(_VIDE)              # 0 = Card(∅)   (= ZERO d'ensembles_entiers)
_SING = E.singleton(_VIDE)           # {∅}  (= 1 comme marqueur ensembliste)
_CARD_SING = cardinal(_SING)         # Card({∅})  (= 1 comme CARDINAL)


# ═══════════════════════════════════════════════════════════════════════════════
# Lemme : Card(∅) = ∅   (« 0 = ∅ », E.III.3.1, Exemple 1)
# ═══════════════════════════════════════════════════════════════════════════════
def cardinal_vide_egale_vide():
    """⊢ Card(∅) = ∅.   (le cardinal du vide EST le vide ; « 0 = ∅ », E.III.3.1, Ex. 1.)

    Tout ensemble est équipotent à son cardinal : Eq(∅, Card∅) (equipotent_son_cardinal,
    version terme).  Une telle équipotence est une bijection F : ∅ → Card∅ ; sa
    SURJECTIVITÉ donne image(F, ∅) = Card∅ ; mais l'image du vide est toujours vide,
    image(F, ∅) = ∅ (image_sur_vide).  Donc ∅ = Card∅, soit Card∅ = ∅.  (Même
    structure de réfutation que vide_non_equipotent_singleton, mais ici l'égalité
    SORT de la bijection au lieu de la réfuter.)  F non libre dans « Card∅ = ∅ » →
    ∃-élimination conclut, sans hypothèse."""
    vF = var("F")
    imgF = E.image(vF, _VIDE)
    bij = est_bijection_de(vF, _VIDE, _ZERO)                  # F bijection ∅ → Card∅
    # surjectivité : image(F, ∅) = Card∅   (2ᵉ conjoint du 2ᵉ conjoint de est_bijection_de)
    surj = conjonction_elim_droite(conjonction_elim_droite(N.assume(bij)))   # image(F,∅) = Card∅
    img_vide = image_sur_vide("F")                           # image(F,∅) = ∅
    # ∅ = image(F,∅) = Card∅ , puis symétrie → Card∅ = ∅
    # (on compose en mettant ∅ — SANS variable F libre — dans le trou Leibniz, pour
    #  éviter le renommage capture-évitant du « F » lié à l'intérieur de Card∅)
    vide_eq_imgF = N.modus_ponens(img_vide, symetrie(imgF, _VIDE))   # ∅ = image(F,∅)
    vide_eq_cVide = composer_egalites(vide_eq_imgF, surj)            # ∅ = Card∅  (sous bij)
    cVide_eq_vide = N.modus_ponens(vide_eq_cVide, symetrie(_VIDE, _ZERO))   # Card∅ = ∅  (sous bij)
    imp = N.loi_deduction(bij, cVide_eq_vide)               # bij ⇒ (Card∅ = ∅)
    elim = existe_elimination(imp, "F")                     # Eq(∅, Card∅) ⇒ (Card∅ = ∅)
    eq_card = _eq_son_cardinal_terme(_VIDE)                 # Eq(∅, Card∅)
    return N.modus_ponens(eq_card, elim)                   # Card∅ = ∅


# ═══════════════════════════════════════════════════════════════════════════════
# « 0 + 1 = 1 » au niveau du SUCCESSEUR :  successeur(0) = Card({∅})
# ═══════════════════════════════════════════════════════════════════════════════
def successeur_zero_egale_un():
    """⊢ successeur(0) = Card({∅}).   (« 0 + 1 = 1 », E.III.4.1.)

    successeur(0) = successeur(Card∅) = somme_cardinale_binaire(Card∅, {∅})
                  = Card(Card∅ ⊔ {∅})        [définition fidèle du successeur].
    Card∅ = ∅ (cardinal_vide_egale_vide) ⇒ Card(Card∅ ⊔ {∅}) = Card(∅ ⊔ {∅})
    [congruence_terme dans le terme Card(· ⊔ {∅})] ; puis Card(∅ ⊔ {∅}) = Card({∅})
    [card_somme_zero_un].  Donc successeur(0) = Card({∅}) = 1."""
    succ0 = Ent.successeur(_ZERO)                           # = Card(Card∅ ⊔ {∅})
    cve = cardinal_vide_egale_vide()                       # Card∅ = ∅
    # Card(Card∅ ⊔ {∅}) = Card(∅ ⊔ {∅})  (réécriture Card∅→∅, trou w en 1ʳᵉ coordonnée)
    trou = cardinal(somme_disjointe(var("w"), _SING))      # Card((w×{0}) ∪ ({∅}×{1}))
    cong = N.modus_ponens(cve, congruence_terme(_ZERO, _VIDE, trou))   # Card(Card∅⊔{∅})=Card(∅⊔{∅})
    csz = card_somme_zero_un()                             # Card(∅ ⊔ {∅}) = Card({∅})
    return composer_egalites(cong, csz)                    # successeur(0) = Card({∅})


# ═══════════════════════════════════════════════════════════════════════════════
# « 0 ≠ 0 + 1 »  :  ¬(0 = successeur(0))
# ═══════════════════════════════════════════════════════════════════════════════
def zero_distinct_successeur_zero():
    """⊢ ¬(0 = 0 + 1).   (« 0 ≠ 0+1 » : le successeur de 0 diffère de 0, E.III.4.1.)

    On a 0 = Card(∅) et 0+1 = successeur(0) = Card({∅}) (successeur_zero_egale_un).
    Or Card(∅) ≠ Card({∅}) : sinon, par la Proposition 1 (sens
    Card X = Card Y ⇒ Eq(X, Y)), on aurait Eq(∅, {∅}), ce que réfute
    vide_non_equipotent_singleton.  Donc ¬(Card∅ = Card{∅}) ; réécriture
    Card{∅} → successeur(0) (Leibniz) conclut ¬(0 = successeur(0))."""
    succ0 = Ent.successeur(_ZERO)
    # ¬(Card∅ = Card{∅})  par contraposée de la Proposition 1 (sens direct ⇐) :
    #   (Card∅ = Card{∅}) ⇒ Eq(∅, {∅})  [equipotent_si_cardinal_egal, version terme]
    gen = N.generalisation("X", N.generalisation("Y",
        equipotent_si_cardinal_egal("X", "Y")))            # (∀X)(∀Y)(Card X=Card Y ⇒ Eq(X,Y))
    esce = instancie(instancie(gen, _VIDE), _SING)         # (Card∅=Card{∅}) ⇒ Eq(∅,{∅})
    notEq = vide_non_equipotent_singleton()                # ¬Eq(∅, {∅})
    # sous (Card∅=Card{∅}) : Eq(∅,{∅}) [esce] contredit ¬Eq → ex falso ⇒ ¬(Card∅=Card{∅})
    h = N.assume(egal(_ZERO, _CARD_SING))
    eqES = N.modus_ponens(h, esce)                         # Eq(∅,{∅})  (sous Card∅=Card{∅})
    falso = N.modus_ponens(eqES, N.modus_ponens(notEq,
        N.s2(non(equipotent(_VIDE, _SING)), non(egal(_ZERO, _CARD_SING)))))   # ¬(Card∅=Card{∅})
    imp = N.loi_deduction(egal(_ZERO, _CARD_SING), falso)  # (Card∅=Card{∅}) ⇒ ¬(Card∅=Card{∅})
    ne_card = N.modus_ponens(imp, N.s1(non(egal(_ZERO, _CARD_SING))))   # ¬(Card∅ = Card{∅})
    # réécrire Card{∅} → successeur(0)  (via successeur(0) = Card{∅}, symétrie + Leibniz)
    succ0_eq_un = successeur_zero_egale_un()               # successeur(0) = Card{∅}
    cSing_eq_succ0 = N.modus_ponens(succ0_eq_un, symetrie(succ0, _CARD_SING))   # Card{∅} = successeur(0)
    leib = N.s6(_CARD_SING, succ0, "w", non(egal(_ZERO, var("w"))))   # (Card{∅}=succ0)⇒(¬(0=Card{∅})⇔¬(0=succ0))
    equiv = N.modus_ponens(cSing_eq_succ0, leib)
    return N.modus_ponens(ne_card, equivalence_avant(equiv))   # ¬(0 = successeur(0))


# ═══════════════════════════════════════════════════════════════════════════════
# « 0 est un cardinal »  (1er conjoint de Fini(0))
# ═══════════════════════════════════════════════════════════════════════════════
def zero_est_un_cardinal():
    """⊢ 0 est un cardinal  =  ⊢ (∃X)(Card(∅) = Card(X))   (E.III.3.1, Déf. 2).

    0 = Card(∅) est de la forme Card(X) (témoin X := ∅) : c'est card_est_un_cardinal
    appliqué à ∅, avec le liant interne « X » (cohérent avec est_cardinal de
    est_fini)."""
    return card_est_un_cardinal(_VIDE, "X")                # est_cardinal(Card∅) = est_cardinal(0)


# ═══════════════════════════════════════════════════════════════════════════════
# « 0 EST UN ENTIER NATUREL »  :  ⊢ Fini(0)   (JALON, E.III.4.1, Déf. 1)
# ═══════════════════════════════════════════════════════════════════════════════
def fini_zero():
    """⊢ Fini(0)  =  (0 est un cardinal) ∧ (0 ≠ 0 + 1).   (0 EST UN ENTIER NATUREL.)

    Déf. 1 (E.III.4.1) : Fini(𝔞) :⇔ (𝔞 cardinal) ∧ (𝔞 ≠ 𝔞+1).  Pour 𝔞 = 0 = Card(∅),
    les DEUX conjoints sont certifiés : zero_est_un_cardinal et
    zero_distinct_successeur_zero.  Leur conjonction EST Fini(0).  C'est le PREMIER
    ENTIER NATUREL CONCRET établi par le noyau (cf. l'itération 0,1,2,… de Bourbaki)."""
    card0 = zero_est_un_cardinal()                         # 0 est un cardinal
    ne = zero_distinct_successeur_zero()                   # 0 ≠ 0+1
    return conjonction_intro(card0, ne)                   # Fini(0)


__all__ = ["cardinal_vide_egale_vide", "successeur_zero_egale_un",
           "zero_distinct_successeur_zero", "zero_est_un_cardinal", "fini_zero"]
