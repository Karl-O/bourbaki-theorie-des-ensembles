"""§III.3.3 — Arithmétique de la SOMME cardinale (E.III.3, Déf. 3 + Cor. de Prop. 5),
miroir EXACT de l'arithmétique du produit (ensembles_arith_cardinale).

DÉBLOQUÉ par le keystone `eq_somme_invariant`
        ⊢ (Eq(A, A₁) et Eq(B, B₁))  ⇒  Eq(A ⊔ B, A₁ ⊔ B₁)
(ensembles_somme_equipotence) et relié aux cardinaux par la Proposition 1
        ⊢ Eq(X, Y) ⇒ (Card X = Card Y)   (sens direct, version TERME _prop1_direct_t).

SOMME CARDINALE BINAIRE.  Bourbaki (Déf. 3, E.III.3.3) pose, pour deux cardinaux
a et b, la somme a + b := Card(a ⊔ b)  (cardinal de la somme disjointe des deux
ensembles a, b — cas à deux indices de la définition par famille ∑_{ι∈I} a_ι).
La somme disjointe binaire est  a ⊔ b := (a×{0}) ∪ (b×{1})  (ensembles_somme_disjointe).

RÉSULTATS (chacun CERTIFIÉ par le noyau et TESTÉ, test_arith_somme.py) :
  • somme_disjointe_cardinal(X,Y,a,b)
        ⊢ (Card X = a et Card Y = b) ⇒ Card(X⊔Y) = somme_cardinale_binaire(a,b)
    — forme finale BIEN-DÉFINIE : Card(X⊔Y) ne dépend QUE de Card X et Card Y
      (la somme cardinale est une opération bien définie sur les cardinaux) ;
  • somme_cardinale_commutative(A,B)
        ⊢ Card(A⊔B) = Card(B⊔A)        (= a + b = b + a, Cor. de Prop. 5) ;
  • somme_cardinale_zero_neutre(B)
        ⊢ Card(∅⊔B) = Card(B)          (0 + b = b, 0 = Card(∅), Cor. 1 de Prop. 6 ;
    le théorème sous-jacent CLOS est card_somme_zero_neutre, ensembles_somme_zero) ;
  • somme_cardinale_associative(A,B,C)
        ⊢ Card((A⊔B)⊔C) = Card(A⊔(B⊔C))   (= (a+b)+c = a+(b+c), Cor. de Prop. 5 ;
    ASSEMBLAGE COMPLET de la bijection de réassociation des copies — fonctionnel,
    domaine, valeur, membre_assoc3 (3 feuilles), injective (3×3), image, bijection,
    Eq — certifié dans ensembles_somme_associe ; relié aux cardinaux par _prop1_direct_t).

La bijection d'échange des copies est construite dans ensembles_somme_commute (swap
des marqueurs), celle de réassociation dans ensembles_somme_associe, sur la MÊME
machinerie liants a,b/c,d que le produit.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, appartient, existe, subst_t)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (equipotent_son_cardinal,
                                           cardinal_egal_si_equipotent)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, somme_cardinale_binaire
from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_somme_equipotence import eq_somme_invariant
from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_somme_commute import eq_somme_commute
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant,
                               instancie)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import symetrie
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import equipotent


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── Ponts équipotence ↔ cardinal (importés de l'arithmétique produit) ─────────
def _eq_son_cardinal_terme(vX):
    """⊢ Eq(T, Card T) pour un TERME T (généralise equipotent_son_cardinal aux termes)."""
    refl_all = N.generalisation("X", equipotent_son_cardinal("X"))   # (∀X) Eq(X, Card X)
    return instancie(refl_all, vX)


def _eq_son_cardinal_reecrit(x, a):
    """{Card X = a} ⊢ Eq(X, a).   (réécriture de Eq(X, Card X) par Card X = a.)"""
    vX, va = _t(x), _t(a)
    cX = cardinal(vX)
    eq_card = equipotent_son_cardinal(x) if isinstance(x, str) \
        else _eq_son_cardinal_terme(vX)               # Eq(X, Card X)
    leib = N.s6(cX, va, "w", equipotent(vX, var("w")))
    h = N.assume(egal(cX, va))                         # Card X = a
    equiv = N.modus_ponens(h, leib)                    # Eq(X, Card X) ⇔ Eq(X, a)
    return N.modus_ponens(eq_card, equivalence_avant(equiv))   # Eq(X, a)   [hyp Card X=a]


def _prop1_direct_t(tU, tV):
    """⊢ Eq(U, V) ⇒ (Card U = Card V) pour des TERMES U, V quelconques.

    Version TERME du sens direct de la Proposition 1 (cardinal_egal_si_equipotent
    n'accepte que des NOMS de variables) : on généralise puis on instancie aux
    termes U, V (robuste grâce au renommage déterministe _fraiche → @0,@1)."""
    gen = N.generalisation("X", N.generalisation("Y",
        cardinal_egal_si_equipotent("X", "Y")))      # (∀X)(∀Y)(Eq(X,Y) ⇒ Card X=Card Y)
    return instancie(instancie(gen, tU), tV)         # Eq(U,V) ⇒ Card U=Card V


# ── (1) FORME FINALE BIEN-DÉFINIE de la somme cardinale ────────────────────────
# NB liants : les cardinaux-paramètres a, b sont nommés « A », « B » (et NON « a »,
# « b ») car le keystone eq_somme_invariant utilise « a », « b » comme liants
# INTERNES des projections pr₁/pr₂ du terme somme (E.couple(pr1(k,"a","b"),…)) ;
# passer var("a")/var("b") comme A₁/B₁ y provoquerait une capture.  « A », « B »
# sont libres de toute collision.
def somme_disjointe_cardinal(x="X", y="Y", a="A", b="B"):
    """⊢ (Card X = a et Card Y = b) ⇒ Card(X⊔Y) = somme_cardinale_binaire(a, b).

    FORME FINALE de la somme cardinale a + b := Card(A⊔B) : Card(X⊔Y) ne dépend QUE
    de Card X et Card Y — la somme cardinale est une opération BIEN DÉFINIE sur les
    cardinaux (E.III.3.3, Déf. 3).  Miroir EXACT de produit_cardinal_bien_defini.

    Preuve : sous Card X = a, Card Y = b, on a Eq(X, a) et Eq(Y, b)
    (equipotent_son_cardinal + réécriture S6) ; le keystone eq_somme_invariant
    donne Eq(X⊔Y, a⊔b) ; la Proposition 1 (sens direct) conclut
    Card(X⊔Y) = Card(a⊔b) = somme_cardinale_binaire(a, b)."""
    vX, vY, va, vb = _t(x), _t(y), _t(a), _t(b)
    cX, cY = cardinal(vX), cardinal(vY)
    XY = somme_disjointe(vX, vY)
    ab = somme_disjointe(va, vb)
    hyp = et(egal(cX, va), egal(cY, vb))
    h = N.assume(hyp)
    hX = conjonction_elim_gauche(h)                    # Card X = a
    hY = conjonction_elim_droite(h)                    # Card Y = b
    # Eq(X, a)  et  Eq(Y, b)
    eqXa = _eq_son_cardinal_reecrit(x, a)              # {Card X=a} ⊢ Eq(X, a)
    eqXa = N.modus_ponens(hX, N.loi_deduction(egal(cX, va), eqXa))
    eqYb = _eq_son_cardinal_reecrit(y, b)              # {Card Y=b} ⊢ Eq(Y, b)
    eqYb = N.modus_ponens(hY, N.loi_deduction(egal(cY, vb), eqYb))
    # Eq(X⊔Y, a⊔b)  via le keystone
    inv = eq_somme_invariant("F", "G", vX, vY, va, vb)   # (Eq(X,a)et Eq(Y,b))⇒Eq(X⊔Y,a⊔b)
    eqXYab = N.modus_ponens(conjonction_intro(eqXa, eqYb), inv)      # Eq(X⊔Y, a⊔b)
    # Card(X⊔Y) = Card(a⊔b)  via Proposition 1 (sens direct, version TERME)
    prop1 = _prop1_direct_t(XY, ab)                    # Eq(X⊔Y, a⊔b) ⇒ Card(X⊔Y)=Card(a⊔b)
    card_eq = N.modus_ponens(eqXYab, prop1)            # Card(X⊔Y) = Card(a⊔b) = a+b
    return N.loi_deduction(hyp, card_eq)


# ── (2) COMMUTATIVITÉ de la somme cardinale ───────────────────────────────────
def somme_cardinale_commutative(a="A", b="B"):
    """⊢ Card(A⊔B) = Card(B⊔A).   (= somme_cardinale_binaire(A,B)
                                     = somme_cardinale_binaire(B,A) ;
       commutativité a + b = b + a, Cor. de Prop. 5, E.III.3.3.)

    Preuve : eq_somme_commute ⊢ Eq(A⊔B, B⊔A) (échange des copies, clos) ; la
    Proposition 1 (sens direct, version TERME) conclut Card(A⊔B) = Card(B⊔A)."""
    va, vb = _t(a), _t(b)
    AB = somme_disjointe(va, vb)
    BA = somme_disjointe(vb, va)
    eq = eq_somme_commute(a, b)                        # Eq(A⊔B, B⊔A)  (clos)
    prop1 = _prop1_direct_t(AB, BA)                    # Eq(A⊔B, B⊔A) ⇒ Card(A⊔B)=Card(B⊔A)
    return N.modus_ponens(eq, prop1)                   # Card(A⊔B) = Card(B⊔A)


# ── (4) 0 ÉLÉMENT NEUTRE de la somme cardinale ────────────────────────────────
def somme_cardinale_zero_neutre(b="B"):
    """⊢ Card(∅⊔B) = Card(B).   (0 + b = b ; 0 = Card(∅), Cor. 1 de Prop. 6, E.III.3.4.)

    Exposé depuis ensembles_somme_zero (bijection témoin v↦(v,1), copie gauche
    ∅×{0} vide) ; la Proposition 1 (sens direct) relie l'équipotence Eq(∅⊔B, B)
    à l'égalité des cardinaux."""
    from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_somme_zero import card_somme_zero_neutre
    return card_somme_zero_neutre(b)


# ── (3) ASSOCIATIVITÉ de la somme cardinale ───────────────────────────────────
def somme_cardinale_associative(a="A", b="B", c="C"):
    """⊢ Card((A⊔B)⊔C) = Card(A⊔(B⊔C)).   (= (a+b)+c = a+(b+c), Cor. de Prop. 5, E.III.3.3.)

    Exposé depuis ensembles_somme_associe (bijection de réassociation des copies,
    assemblage complet : fonctionnel/domaine/valeur/membre_assoc3/injective/image/
    bijection/Eq) ; la Proposition 1 (sens direct) relie Eq((A⊔B)⊔C, A⊔(B⊔C)) à
    l'égalité des cardinaux."""
    from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_somme_associe import somme_cardinale_associative as _assoc
    return _assoc(a, b, c)


__all__ = ["somme_disjointe_cardinal", "somme_cardinale_binaire",
           "somme_cardinale_commutative", "somme_cardinale_zero_neutre",
           "somme_cardinale_associative"]
