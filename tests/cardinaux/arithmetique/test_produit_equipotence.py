"""Tests — §III.3 invariance du produit par équipotence (ensembles_produit_equipotence).

THÉORÈME COMPLET (verrou « liant valeur » levé via le liant exotique « c » des
valeurs du terme produit + la primitive noyau alpha_tau/CS1) :

        ⊢ (Eq(X, X₁) et Eq(Y, Y₁))  ⇒  Eq(X×Y, X₁×Y₁).

Le graphe produit  H = graphe_terme(X×Y, (F(pr₁k), G(pr₂k)))  est fonctionnel, de
domaine X×Y, de valeur (F(pr₁u),G(pr₂u)), injectif (sous F,G injectives) et
d'image X₁×Y₁ (sous F,G surjectives) ; l'assemblage donne la bijection produit.
"""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique import ensembles_produit_equipotence as PE
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, subst_t
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de, equipotent


def test_produit_graphe_fonctionnel_clos():
    """PALIER 1a — ⊢ H est fonctionnel, conclusion EXACTE, théorème CLOS."""
    thm = PE.produit_graphe_fonctionnel()
    H = PE._prod_graphe("F", "G", "X", "Y", "k")
    assert thm.conclusion == E.est_fonctionnel(H)
    assert thm.est_clos


def test_produit_graphe_fonctionnel_termes():
    """Le palier 1a tient quand X, Y sont des TERMES composés (X×Y, Card X, …)."""
    X1 = E.produit(var("A"), var("B"))
    thm = PE.produit_graphe_fonctionnel("F", "G", X1, "Y")
    H = PE._prod_graphe("F", "G", X1, "Y", "k")
    assert thm.conclusion == E.est_fonctionnel(H)
    assert thm.est_clos


def test_produit_graphe_domaine_clos():
    """PALIER 1 — ⊢ dom H = X×Y, conclusion EXACTE, théorème CLOS."""
    thm = PE.produit_graphe_domaine()
    H = PE._prod_graphe("F", "G", "X", "Y", "k")
    A = E.produit(var("X"), var("Y"))
    assert thm.conclusion == egal(E.dom(H), A)
    assert thm.est_clos


def test_produit_graphe_valeur():
    """PALIER 2 — {u∈X×Y} ⊢ H(u) = (F(pr₁u), G(pr₂u)) ; hyp EXACTE u∈X×Y."""
    thm = PE.produit_graphe_valeur()
    H = PE._prod_graphe("F", "G", "X", "Y", "k")
    A = E.produit(var("X"), var("Y"))
    T = PE._prod_terme("F", "G", "k")
    Tu = subst_t(var("u"), "k", T)
    assert thm.conclusion == egal(E.valeur(H, var("u")), Tu)
    assert thm.hypotheses == frozenset({E.appartient(var("u"), A)})


def test_produit_graphe_injective():
    """PALIER 3 — ⊢ injective_dans(H, X×Y) sous {inj F sur X, inj G sur Y}."""
    thm = PE.produit_graphe_injective()
    H = PE._prod_graphe("F", "G", "X", "Y", "k")
    A = E.produit(var("X"), var("Y"))
    assert thm.conclusion == E.injective_dans(H, A)
    assert thm.hypotheses == frozenset({
        E.injective_dans(var("F"), var("X")),
        E.injective_dans(var("G"), var("Y")),
    })


def test_produit_graphe_image():
    """PALIER 4 — ⊢ image(H, X×Y) = X₁×Y₁ sous {F,G func + domaines + images}."""
    thm = PE.produit_graphe_image()
    H = PE._prod_graphe("F", "G", "X", "Y", "k")
    A = E.produit(var("X"), var("Y"))
    X1Y1 = E.produit(var("X1"), var("Y1"))
    assert thm.conclusion == egal(E.image(H, A), X1Y1)
    assert thm.hypotheses == frozenset({
        E.est_fonctionnel(var("F")), egal(E.dom(var("F")), var("X")),
        egal(E.image(var("F"), var("X")), var("X1")),
        E.est_fonctionnel(var("G")), egal(E.dom(var("G")), var("Y")),
        egal(E.image(var("G"), var("Y")), var("Y1")),
    })


def test_produit_est_bijection():
    """PALIER 5a — ⊢ est_bijection_de(H, X×Y, X₁×Y₁) sous {bij F:X→X₁, bij G:Y→Y₁}."""
    thm = PE.produit_est_bijection()
    H = PE._prod_graphe("F", "G", "X", "Y", "k")
    A = E.produit(var("X"), var("Y"))
    X1Y1 = E.produit(var("X1"), var("Y1"))
    assert thm.conclusion == est_bijection_de(H, A, X1Y1)
    assert thm.hypotheses == frozenset({
        est_bijection_de(var("F"), var("X"), var("X1")),
        est_bijection_de(var("G"), var("Y"), var("Y1")),
    })


def test_eq_produit_invariant_clos():
    """PALIER 5 — ⊢ (Eq(X,X₁) et Eq(Y,Y₁)) ⇒ Eq(X×Y, X₁×Y₁), théorème CLOS.

    Invariance du produit par équipotence : keystone de l'arithmétique cardinale."""
    thm = PE.eq_produit_invariant()
    A = E.produit(var("X"), var("Y"))
    X1Y1 = E.produit(var("X1"), var("Y1"))
    target = E.impl(et(equipotent(var("X"), var("X1")), equipotent(var("Y"), var("Y1"))),
                    equipotent(A, X1Y1))
    assert thm.conclusion == target
    assert thm.est_clos


def test_eq_produit_invariant_termes():
    """Robustesse arithmétique : l'invariance tient sur des TERMES composés
    (ex. X = Card U) — débloque produit_cardinal bien défini."""
    CU = E.app("card", var("U"))
    thm = PE.eq_produit_invariant("F", "G", CU, "Y", "X1", "Y1")
    A = E.produit(CU, var("Y"))
    X1Y1 = E.produit(var("X1"), var("Y1"))
    target = E.impl(et(equipotent(CU, var("X1")), equipotent(var("Y"), var("Y1"))),
                    equipotent(A, X1Y1))
    assert thm.conclusion == target
    assert thm.est_clos
