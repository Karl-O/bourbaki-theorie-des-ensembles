"""§III.3.4 — Proposition 8 : le successeur cardinal est INJECTIF.

ÉNONCÉ (E.III.3.4, Prop. 8, lu verbatim ROADMAP_chap2-4.md) :
        « Si a et b sont des cardinaux tels que a + 1 = b + 1, on a a = b. »

Avec le successeur redéfini FIDÈLEMENT (ensembles_entiers.py) comme la somme
cardinale  successeur(𝔞) := 𝔞 + 1 := somme_cardinale_binaire(𝔞, {∅}) =
Card(𝔞 ⊔ {∅})  (1 = Card({∅}), E.III.3.1, Déf. 2, Exemple), la Proposition 8
s'énonce, pour deux ensembles A, B :

        Card(A ⊔ {∅}) = Card(B ⊔ {∅})   ⇒   Card A = Card B.

C'est un GATEWAY de l'arithmétique des entiers : il déduit Fini(1)/Fini(2) et
prépare la récurrence (la classe des cardinaux finis est stable par successeur,
Prop. 1 §III.4.1).

──────────────────────────────────────────────────────────────────────────────
STRUCTURE DE LA PREUVE (réduction en deux maillons) :

  (1) GATEWAY ⟸ Proposition 1 (sens réciproque, version TERME).  L'hypothèse
      successeur(A) = successeur(B) EST  Card(A⊔{∅}) = Card(B⊔{∅})  (le successeur
      est littéralement ce cardinal).  Par la Proposition 1 (Card U = Card V ⇒
      Eq(U, V), equipotent_si_cardinal_egal généralisé aux termes), on obtient
                    Eq(A ⊔ {∅},  B ⊔ {∅}).

  (2) CŒUR (back-and-forth à un coup) — REPORTÉ ⟹ d'une bijection
      h : A⊔{∅} → B⊔{∅} on construit une bijection A → B en DÉPLAÇANT l'élément
      marqué * = (∅, 1) :
          • si h(*) = ** (le * de droite), restreindre h à A ;
          • sinon h(*) = (b₀, 0) ∈ B×{0} et il existe a₀ ∈ A avec h((a₀,0)) = **,
            on échange  a₀ ↦ b₀  et on garde h ailleurs.
      D'où  Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A, B).

  (3) CONCLUSION ⟸ Proposition 1 (sens direct, _prop1_direct_t) : Eq(A, B) ⇒
      Card A = Card B.

Les maillons (1) et (3) sont CERTIFIÉS et CLOS ici.  Le maillon (2) — la
construction back-and-forth de la bijection A → B (analyse de cas sur l'image du
marqueur + reconstruction de bijection au niveau du GRAPHE) — est la partie DURE,
de la même catégorie que les bijections somme/produit/réassociation (≈ un round
complet chacune) ; il est REPORTÉ honnêtement (cf. `reduction_back_and_forth`,
qui ASSEMBLE la Proposition 8 MODULO ce seul lemme, certifié-conditionnel).

──────────────────────────────────────────────────────────────────────────────
THÉORÈMES CERTIFIÉS (chacun testé, cf. test_prop8_successeur.py) :
  • prop1_reciproque_t(U, V)        (clos)  — Card U = Card V ⇒ Eq(U, V)  (Prop. 1
        sens réciproque, TERME-tolérant ; miroir de _prop1_direct_t) ;
  • successeur_egale_card_somme(A)  (clos)  — successeur(A) = Card(A ⊔ {∅})
        (la définition fidèle, par réflexivité) ;
  • successeur_egal_implique_eq_somme(A, B)  (clos)  — successeur(A)=successeur(B)
        ⇒ Eq(A ⊔ {∅}, B ⊔ {∅})   (LE GATEWAY, maillon (1)) ;
  • eq_implique_eq_somme_un(A, B)   (clos)  — Eq(A, B) ⇒ Eq(A ⊔ {∅}, B ⊔ {∅})
        (sens FACILE / réciproque de Prop. 8 : le successeur est monotone pour
        l'équipotence ; via eq_somme_invariant + réflexivité sur le marqueur) ;
  • reduction_back_and_forth(A, B)  (clos, CONDITIONNEL au cœur)  —
        (Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A, B))  ⇒
        (successeur(A) = successeur(B) ⇒ Card A = Card B)
        — la Proposition 8 ASSEMBLÉE modulo le seul lemme back-and-forth.

REPORTÉ honnêtement (anti-faux) : le cœur back-and-forth (2) lui-même, soit
        eq_somme_un_implique_eq(A, B) : Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A, B),
et donc la forme INCONDITIONNELLE  prop8_successeur_injectif :
        Card(A⊔{∅}) = Card(B⊔{∅}) ⇒ Card A = Card B.
Raison : construction d'une bijection par analyse de cas sur l'image du marqueur
* = (∅,1) (cas h(*)=** vs cas échange a₀↦b₀), au niveau du graphe, avec sélecteur
τ et reconstruction — même catégorie de difficulté que les bijections
somme/produit/réassoc, non tenue dans le budget de cet agent.  Le GATEWAY (1) et
l'ASSEMBLAGE modulo (4) sont posés et certifiés : finir Prop. 8 ne demande plus
que le seul lemme back-and-forth.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, impl, et
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.cardinaux.ensembles_cardinaux_theoremes import equipotent_si_cardinal_egal
from bourbaki.cardinaux.ensembles_equipotence import equipotence_reflexive
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.cardinaux.arithmetique.ensembles_somme_equipotence import eq_somme_invariant
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
from bourbaki.entiers import ensembles_entiers as Ent
from bourbaki.logique.tactiques.tactiques_abrege2 import instancie, conjonction_intro
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# Le marqueur de droite 1 = {∅} (E.III.3.1, Déf. 2, Exemple).
_SING = E.singleton(E.VIDE)


# ═══════════════════════════════════════════════════════════════════════════════
# Proposition 1, SENS RÉCIPROQUE, version TERME  (miroir de _prop1_direct_t)
# ═══════════════════════════════════════════════════════════════════════════════
def prop1_reciproque_t(tU, tV):
    """⊢ (Card U = Card V) ⇒ Eq(U, V)   pour des TERMES U, V quelconques.

    Version TERME du sens réciproque de la Proposition 1
    (equipotent_si_cardinal_egal n'accepte que des NOMS de variables) : on
    généralise le sens réciproque en X, Y puis on instancie aux termes U, V
    (robuste grâce au renommage déterministe _fraiche → @0, @1).  Miroir exact de
    _prop1_direct_t (ensembles_arith_cardinale)."""
    gen = N.generalisation("X", N.generalisation("Y",
        equipotent_si_cardinal_egal("X", "Y")))      # (∀X)(∀Y)(Card X=Card Y ⇒ Eq(X,Y))
    return instancie(instancie(gen, _t(tU)), _t(tV))  # Card U=Card V ⇒ Eq(U,V)


# ═══════════════════════════════════════════════════════════════════════════════
# successeur(A) = Card(A ⊔ {∅})   (la définition fidèle, par réflexivité)
# ═══════════════════════════════════════════════════════════════════════════════
def successeur_egale_card_somme(a="A"):
    """⊢ successeur(A) = Card(A ⊔ {∅}).   (déf. fidèle du successeur ; clos.)

    successeur(𝔞) := somme_cardinale_binaire(𝔞, {∅}) := Card(𝔞 ⊔ {∅}) est
    LITTÉRALEMENT ce cardinal (ensembles_entiers.successeur) — l'égalité est une
    réflexivité, qui sert d'ancrage de forme entre le langage des entiers
    (successeur) et celui de la somme cardinale (Card(·⊔{∅}))."""
    va = _t(a)
    return N.reflexivite(Ent.successeur(va))          # successeur(A) = Card(A⊔{∅})


# ═══════════════════════════════════════════════════════════════════════════════
# GATEWAY :  successeur(A) = successeur(B)  ⇒  Eq(A ⊔ {∅}, B ⊔ {∅})   (maillon 1)
# ═══════════════════════════════════════════════════════════════════════════════
def successeur_egal_implique_eq_somme(a="A", b="B"):
    """⊢ (successeur(A) = successeur(B)) ⇒ Eq(A ⊔ {∅}, B ⊔ {∅}).   (gateway ; clos.)

    L'hypothèse successeur(A)=successeur(B) EST Card(A⊔{∅})=Card(B⊔{∅}) (le
    successeur est littéralement ce cardinal).  La Proposition 1 (sens réciproque,
    version TERME) en tire directement Eq(A⊔{∅}, B⊔{∅}).  C'est la moitié SÛRE de
    la Proposition 8 : on remonte de l'égalité des successeurs à l'équipotence des
    ensembles augmentés ; reste à en déduire Eq(A, B) (cœur back-and-forth)."""
    va, vb = _t(a), _t(b)
    AS = somme_disjointe(va, _SING)                   # A ⊔ {∅}
    BS = somme_disjointe(vb, _SING)                   # B ⊔ {∅}
    succA = Ent.successeur(va)                         # = Card(A⊔{∅})
    succB = Ent.successeur(vb)                         # = Card(B⊔{∅})
    h = N.assume(egal(succA, succB))                  # Card(A⊔{∅}) = Card(B⊔{∅})
    recip = prop1_reciproque_t(AS, BS)                # Card(A⊔{∅})=Card(B⊔{∅}) ⇒ Eq(A⊔{∅},B⊔{∅})
    eqABS = N.modus_ponens(h, recip)                  # Eq(A⊔{∅}, B⊔{∅})   [sous l'hyp]
    return N.loi_deduction(egal(succA, succB), eqABS)


# ═══════════════════════════════════════════════════════════════════════════════
# SENS FACILE (converse) :  Eq(A, B)  ⇒  Eq(A ⊔ {∅}, B ⊔ {∅})   (successeur monotone)
# ═══════════════════════════════════════════════════════════════════════════════
def eq_implique_eq_somme_un(a="A", b="B"):
    """⊢ Eq(A, B) ⇒ Eq(A ⊔ {∅}, B ⊔ {∅}).   (sens FACILE ; clos.)

    Direction triviale de la « bijectivité » du successeur : si A et B sont
    équipotents, leurs augmentés A⊔{∅}, B⊔{∅} le sont aussi — on augmente les DEUX
    copies de la MÊME marque {∅}.  Preuve : l'invariance de la somme cardinale
    (eq_somme_invariant) appliquée à Eq(A,B) et à Eq({∅},{∅}) (réflexivité de
    l'équipotence sur le marqueur, instanciée au terme {∅}) donne directement
    Eq(A⊔{∅}, B⊔{∅}).  (C'est la réciproque de la Proposition 8 ; le sens DIFFICILE
    Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B) est le cœur back-and-forth reporté.)"""
    va, vb = _t(a), _t(b)
    AS = somme_disjointe(va, _SING)                   # A ⊔ {∅}
    BS = somme_disjointe(vb, _SING)                   # B ⊔ {∅}
    hAB = N.assume(equipotent(va, vb))                # Eq(A, B)
    refl_all = N.generalisation("X", equipotence_reflexive("X"))   # (∀X) Eq(X, X)
    refl_sing = instancie(refl_all, _SING)            # Eq({∅}, {∅})  (réflexivité sur le marqueur)
    inv = eq_somme_invariant("F", "G", va, _SING, vb, _SING)   # (Eq(A,B) et Eq({∅},{∅})) ⇒ Eq(A⊔{∅},B⊔{∅})
    eqABS = N.modus_ponens(conjonction_intro(hAB, refl_sing), inv)   # Eq(A⊔{∅}, B⊔{∅})  [sous Eq(A,B)]
    return N.loi_deduction(equipotent(va, vb), eqABS)


# ═══════════════════════════════════════════════════════════════════════════════
# ASSEMBLAGE de la Proposition 8 MODULO le cœur back-and-forth   (maillon 4)
# ═══════════════════════════════════════════════════════════════════════════════
def reduction_back_and_forth(a="A", b="B"):
    """⊢ (Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A, B))
            ⇒ ((successeur(A) = successeur(B)) ⇒ (Card A = Card B)).

    ASSEMBLAGE de la Proposition 8 modulo le SEUL lemme back-and-forth
    H := (Eq(A⊔{∅}, B⊔{∅}) ⇒ Eq(A, B)) — la partie DURE, reportée.  Sous H :
        successeur(A)=successeur(B) ⇒[gateway] Eq(A⊔{∅},B⊔{∅}) ⇒[H] Eq(A,B)
                                  ⇒[Prop.1 sens direct, _prop1_direct_t] Card A=Card B.
    Donc finir la Proposition 8 (forme inconditionnelle prop8_successeur_injectif)
    ne demande plus QUE de prouver H = eq_somme_un_implique_eq.  Théorème CLOS
    (l'unique hypothèse H est déchargée par loi_deduction), CONDITIONNEL au cœur."""
    va, vb = _t(a), _t(b)
    AS = somme_disjointe(va, _SING)                   # A ⊔ {∅}
    BS = somme_disjointe(vb, _SING)                   # B ⊔ {∅}
    succA = Ent.successeur(va)
    succB = Ent.successeur(vb)
    hard = impl(equipotent(AS, BS), equipotent(va, vb))   # H : le cœur back-and-forth
    H = N.assume(hard)
    gateway = successeur_egal_implique_eq_somme(a, b)  # succ(A)=succ(B) ⇒ Eq(A⊔{∅},B⊔{∅})
    prop1dir = _prop1_direct_t(va, vb)                 # Eq(A,B) ⇒ Card A=Card B
    # succ(A)=succ(B) ⇒ Eq(A⊔{∅},B⊔{∅}) ⇒[H] Eq(A,B) ⇒ Card A=Card B
    chain = syllogisme(gateway, syllogisme(H, prop1dir))   # succ=succ ⇒ Card A=Card B   [sous H]
    return N.loi_deduction(hard, chain)


__all__ = ["prop1_reciproque_t", "successeur_egale_card_somme",
           "successeur_egal_implique_eq_somme", "eq_implique_eq_somme_un",
           "reduction_back_and_forth"]
