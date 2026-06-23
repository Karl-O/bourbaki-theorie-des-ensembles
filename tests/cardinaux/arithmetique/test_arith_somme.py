"""Tests §III.3.3 — Arithmétique de la somme cardinale binaire a+b := Card(a⊔b).

  • somme_disjointe_cardinal     : Card(X⊔Y) ne dépend que de Card X, Card Y ;
  • somme_cardinale_commutative  : a+b = b+a  (Card(A⊔B) = Card(B⊔A)) ;
  • somme_cardinale_zero_neutre  : 0+b = b  (Card(∅⊔B) = Card B) ;
  • somme_cardinale_associative  : (a+b)+c = a+(b+c)  (Card((A⊔B)⊔C)=Card(A⊔(B⊔C))).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, subst_t
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_bijection_de, equipotent
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, somme_cardinale_binaire, ZERO
from bourbaki.cardinaux.arithmetique import ensembles_arith_somme as S


def test_somme_cardinale_binaire_def():
    """a+b = Card(a⊔b)  (forme exacte du terme somme cardinale binaire)."""
    va, vb = var("A"), var("B")
    assert somme_cardinale_binaire(va, vb) == cardinal(somme_disjointe(va, vb))


def test_somme_disjointe_cardinal():
    """(1) ⊢ (Card X = a et Card Y = b) ⇒ Card(X⊔Y) = a+b, CLOS.

    La somme cardinale Card(X⊔Y) ne dépend QUE de Card X et Card Y."""
    vX, vY, vA, vB = var("X"), var("Y"), var("A"), var("B")
    cX, cY = cardinal(vX), cardinal(vY)
    XY = somme_disjointe(vX, vY)
    t = S.somme_disjointe_cardinal("X", "Y", "A", "B")
    target = impl(et(egal(cX, vA), egal(cY, vB)),
                  egal(cardinal(XY), somme_cardinale_binaire(vA, vB)))
    assert t.conclusion == target
    assert t.est_clos


def test_somme_disjointe_cardinal_termes():
    """Robustesse : la bien-définition tient quand X est un TERME composé (X = U⊔V)."""
    U, V = var("U"), var("V")
    t = S.somme_disjointe_cardinal(somme_disjointe(U, V), "Y", "A", "B")
    assert t.est_clos


def test_somme_cardinale_commutative():
    """(2) ⊢ Card(A⊔B) = Card(B⊔A)  (= a+b = b+a), CLOS."""
    vA, vB = var("A"), var("B")
    AB = somme_disjointe(vA, vB)
    BA = somme_disjointe(vB, vA)
    t = S.somme_cardinale_commutative("A", "B")
    assert t.conclusion == egal(cardinal(AB), cardinal(BA))
    assert t.est_clos
    # forme somme cardinale binaire : scb(A,B) = scb(B,A)
    assert t.conclusion == egal(somme_cardinale_binaire(vA, vB),
                                somme_cardinale_binaire(vB, vA))


def test_somme_cardinale_associative():
    """(3) ⊢ Card((A⊔B)⊔C) = Card(A⊔(B⊔C))  (= (a+b)+c = a+(b+c)), CLOS."""
    vA, vB, vC = var("A"), var("B"), var("C")
    ABC_g = somme_disjointe(somme_disjointe(vA, vB), vC)
    ABC_d = somme_disjointe(vA, somme_disjointe(vB, vC))
    t = S.somme_cardinale_associative("A", "B", "C")
    assert t.conclusion == egal(cardinal(ABC_g), cardinal(ABC_d))
    assert t.est_clos
