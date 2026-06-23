"""Tests §III.3.3 — Arithmétique du produit cardinal binaire a·b := Card(a×b).

  • produit_cardinal_bien_defini : Card(X×Y) ne dépend que de Card X, Card Y ;
  • produit_cardinal_commutatif  : a·b = b·a  (Card(X×Y) = Card(Y×X)).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, subst_t
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_bijection_de, equipotent
from bourbaki.cardinaux.arithmetique.iii_3_3_produit import ensembles_arith_cardinale as A


def test_produit_cardinal_binaire_def():
    """a·b = Card(a×b)  (forme exacte du terme produit cardinal binaire)."""
    va, vb = var("A"), var("B")
    assert A.produit_cardinal_binaire(va, vb) == cardinal(E.produit(va, vb))


def test_produit_cardinal_bien_defini():
    """(1) ⊢ (Card X = a et Card Y = b) ⇒ Card(X×Y) = a·b, CLOS.

    Le produit cardinal Card(X×Y) ne dépend QUE de Card X et Card Y."""
    vX, vY, vA, vB = var("X"), var("Y"), var("A"), var("B")
    cX, cY = cardinal(vX), cardinal(vY)
    XY = E.produit(vX, vY)
    t = A.produit_cardinal_bien_defini("X", "Y", "A", "B")
    target = impl(et(egal(cX, vA), egal(cY, vB)),
                  egal(cardinal(XY), A.produit_cardinal_binaire(vA, vB)))
    assert t.conclusion == target
    assert t.est_clos


def test_produit_cardinal_bien_defini_termes():
    """Robustesse : la bien-définition tient quand X est un TERME composé (X = U×V)."""
    U, V = var("U"), var("V")
    t = A.produit_cardinal_bien_defini(E.produit(U, V), "Y", "A", "B")
    assert t.est_clos


def test_produit_cardinal_commutatif():
    """(2) ⊢ Card(X×Y) = Card(Y×X)  (= a·b = b·a), CLOS."""
    vX, vY = var("X"), var("Y")
    XY = E.produit(vX, vY)
    YX = E.produit(vY, vX)
    t = A.produit_cardinal_commutatif("X", "Y")
    assert t.conclusion == egal(cardinal(XY), cardinal(YX))
    assert t.est_clos
    # forme produit cardinal binaire : pcb(X,Y) = pcb(Y,X)
    assert t.conclusion == egal(A.produit_cardinal_binaire(vX, vY),
                                A.produit_cardinal_binaire(vY, vX))


def test_reassoc_graphe_fonctionnel():
    """(3, fondation) ⊢ R fonctionnel, R = graphe de ((x,y),z)↦(x,(y,z)), CLOS."""
    t = A.reassoc_graphe_fonctionnel("X", "Y", "Z")
    R = A._reassoc_graphe("X", "Y", "Z", "k")
    assert t.conclusion == E.est_fonctionnel(R)
    assert t.est_clos


def test_reassoc_graphe_domaine():
    """(3, fondation) ⊢ dom(R) = (X×Y)×Z, CLOS."""
    t = A.reassoc_graphe_domaine("X", "Y", "Z")
    R = A._reassoc_graphe("X", "Y", "Z", "k")
    Axyz = E.produit(E.produit(var("X"), var("Y")), var("Z"))
    assert t.conclusion == egal(E.dom(R), Axyz)
    assert t.est_clos


def test_reassoc_graphe_valeur():
    """(3.1) {u∈(X×Y)×Z} ⊢ R(u) = (pr₁(pr₁u), (pr₂(pr₁u), pr₂u))."""
    from bourbaki.logique.i_1_termes_relations.formule import appartient
    t = A.reassoc_graphe_valeur("X", "Y", "Z", "u")
    R = A._reassoc_graphe("X", "Y", "Z", "k")
    Tu = subst_t(var("u"), "k", A._reassoc_terme("k"))
    Axyz = E.produit(E.produit(var("X"), var("Y")), var("Z"))
    assert t.conclusion == egal(E.valeur(R, var("u")), Tu)
    # unique hypothèse : u∈(X×Y)×Z
    assert list(t.hypotheses) == [appartient(var("u"), Axyz)]


def test_reassoc_graphe_injective():
    """(3.2) ⊢ injective_dans(R, (X×Y)×Z), CLOS."""
    t = A.reassoc_graphe_injective("X", "Y", "Z")
    R = A._reassoc_graphe("X", "Y", "Z", "k")
    Axyz = E.produit(E.produit(var("X"), var("Y")), var("Z"))
    assert t.conclusion == E.injective_dans(R, Axyz)
    assert t.est_clos


def test_reassoc_graphe_image():
    """(3.3) ⊢ image(R, (X×Y)×Z) = X×(Y×Z), CLOS  (surjectivité)."""
    t = A.reassoc_graphe_image("X", "Y", "Z")
    R = A._reassoc_graphe("X", "Y", "Z", "k")
    Axyz = E.produit(E.produit(var("X"), var("Y")), var("Z"))
    XYZ = E.produit(var("X"), E.produit(var("Y"), var("Z")))
    assert t.conclusion == egal(E.image(R, Axyz), XYZ)
    assert t.est_clos


def test_reassoc_est_bijection():
    """(3.4) ⊢ est_bijection_de(R, (X×Y)×Z, X×(Y×Z)), CLOS."""
    t = A.reassoc_est_bijection("X", "Y", "Z")
    R = A._reassoc_graphe("X", "Y", "Z", "k")
    Axyz = E.produit(E.produit(var("X"), var("Y")), var("Z"))
    XYZ = E.produit(var("X"), E.produit(var("Y"), var("Z")))
    assert t.conclusion == est_bijection_de(R, Axyz, XYZ)
    assert t.est_clos


def test_eq_produit_associatif():
    """(3.4) ⊢ Eq((X×Y)×Z, X×(Y×Z)), CLOS  (associativité à équipotence près)."""
    t = A.eq_produit_associatif("X", "Y", "Z")
    Axyz = E.produit(E.produit(var("X"), var("Y")), var("Z"))
    XYZ = E.produit(var("X"), E.produit(var("Y"), var("Z")))
    assert t.conclusion == equipotent(Axyz, XYZ)
    assert t.est_clos


def test_produit_cardinal_associatif():
    """(3.5) ⊢ Card((X×Y)×Z) = Card(X×(Y×Z)), CLOS  (a·(b·c) = (a·b)·c).

    Les liants des cardinaux sont les noms FRAIS capture-évitants @0/@1 (le terme
    argument contient « Z » libre, qui entrerait en collision avec le liant Z par
    défaut de cardinal ; la Proposition 1 via _prop1_direct_t produit la forme
    correcte sans capture)."""
    Axyz = E.produit(E.produit(var("X"), var("Y")), var("Z"))
    XYZ = E.produit(var("X"), E.produit(var("Y"), var("Z")))
    t = A.produit_cardinal_associatif("X", "Y", "Z")
    assert t.conclusion == egal(cardinal(Axyz, "@0"), cardinal(XYZ, "@1"))
    assert t.est_clos
