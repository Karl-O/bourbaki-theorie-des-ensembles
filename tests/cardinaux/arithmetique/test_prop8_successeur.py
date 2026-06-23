"""Tests §III.3.4 — Proposition 8 : successeur cardinal INJECTIF
(a + 1 = b + 1 ⇒ a = b), réduction certifiée.

Vérifie les maillons SÛRS de la Proposition 8 (conclusions exactes + closdes) :
  • prop1_reciproque_t              : Card U = Card V ⇒ Eq(U, V)  (Prop. 1 ⇐, TERME) ;
  • successeur_egale_card_somme     : successeur(A) = Card(A ⊔ {∅})  (déf. fidèle) ;
  • successeur_egal_implique_eq_somme : succ(A)=succ(B) ⇒ Eq(A⊔{∅},B⊔{∅})  (GATEWAY) ;
  • eq_implique_eq_somme_un         : Eq(A, B) ⇒ Eq(A⊔{∅},B⊔{∅})  (sens facile) ;
  • reduction_back_and_forth        : (Eq(A⊔{∅},B⊔{∅})⇒Eq(A,B)) ⇒
                                      (succ(A)=succ(B) ⇒ Card A = Card B)  (assemblage
                                      MODULO le seul cœur back-and-forth reporté).
"""
from bourbaki.logique.formule import var, egal, impl
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers import ensembles_entiers as Ent
from bourbaki.cardinaux.arithmetique import ensembles_prop8_successeur as P8


_SING = E.singleton(E.VIDE)


def _AS(t):
    return somme_disjointe(t, _SING)


def test_prop1_reciproque_t():
    """⊢ (Card U = Card V) ⇒ Eq(U, V) sur des TERMES quelconques, CLOS."""
    A, B = var("A"), var("B")
    AS, BS = _AS(A), _AS(B)
    t = P8.prop1_reciproque_t(AS, BS)
    target = impl(egal(cardinal(AS), cardinal(BS)), equipotent(AS, BS))
    assert t.conclusion == target
    assert t.est_clos


def test_prop1_reciproque_t_noms():
    """Le sens réciproque tient aussi sur des noms simples X, Y, CLOS."""
    X, Y = var("X"), var("Y")
    t = P8.prop1_reciproque_t(X, Y)
    assert t.conclusion == impl(egal(cardinal(X), cardinal(Y)), equipotent(X, Y))
    assert t.est_clos


def test_successeur_egale_card_somme():
    """⊢ successeur(A) = Card(A ⊔ {∅})  (définition fidèle du successeur), CLOS."""
    A = var("A")
    t = P8.successeur_egale_card_somme(A)
    assert t.conclusion == egal(Ent.successeur(A), cardinal(_AS(A)))
    assert t.est_clos


def test_gateway():
    """⊢ (successeur(A)=successeur(B)) ⇒ Eq(A⊔{∅}, B⊔{∅})  (GATEWAY), CLOS."""
    A, B = var("A"), var("B")
    t = P8.successeur_egal_implique_eq_somme(A, B)
    target = impl(egal(Ent.successeur(A), Ent.successeur(B)),
                  equipotent(_AS(A), _AS(B)))
    assert t.conclusion == target
    assert t.est_clos


def test_eq_implique_eq_somme_un():
    """⊢ Eq(A, B) ⇒ Eq(A⊔{∅}, B⊔{∅})  (sens facile : successeur monotone), CLOS."""
    A, B = var("A"), var("B")
    t = P8.eq_implique_eq_somme_un(A, B)
    target = impl(equipotent(A, B), equipotent(_AS(A), _AS(B)))
    assert t.conclusion == target
    assert t.est_clos


def test_reduction_back_and_forth():
    """⊢ (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B)) ⇒ (succ(A)=succ(B) ⇒ Card A=Card B), CLOS.

    Proposition 8 ASSEMBLÉE modulo le seul cœur back-and-forth : tout est certifié
    sauf l'hypothèse H = (Eq(A⊔{∅},B⊔{∅}) ⇒ Eq(A,B)), déchargée par loi_deduction."""
    A, B = var("A"), var("B")
    AS, BS = _AS(A), _AS(B)
    t = P8.reduction_back_and_forth(A, B)
    hard = impl(equipotent(AS, BS), equipotent(A, B))
    inner = impl(egal(Ent.successeur(A), Ent.successeur(B)),
                 egal(cardinal(A), cardinal(B)))
    assert t.conclusion == impl(hard, inner)
    assert t.est_clos


def test_reduction_back_and_forth_termes():
    """Robustesse : la réduction tient quand A est un TERME composé (A = U×V)."""
    U, V = var("U"), var("V")
    t = P8.reduction_back_and_forth(E.produit(U, V), "B")
    assert t.est_clos
