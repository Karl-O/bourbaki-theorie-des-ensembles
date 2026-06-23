"""Tests §III.3 — Théorème de Cantor, étape 1 : X ≤ P(X)  (injection x↦{x}).

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et, pour les
théorèmes clos, est_clos ; pour les lemmes conditionnels, l'ensemble des
hypothèses attendues.
"""
from bourbaki.logique.formule import (var, egal, et, impl, non, appartient, inclus, equiv)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_cantor as C
from bourbaki.cardinaux.ensembles_cardinaux import (est_injection_de, inf_egal_card, est_bijection_de,
                                 equipotent, inf_strict_card)


def _G(x="X"):
    return C._singleton_graphe(x)


def test_graphe_terme_domaine():
    X = var("X")
    T = E.singleton(var("x"))
    thm = C.graphe_terme_domaine(X, T, "x", "y", "z")
    assert thm.conclusion == egal(E.dom(E.graphe_terme(X, T, "x")), X)
    assert thm.est_clos


def test_graphe_terme_valeur():
    X, u = var("X"), var("u")
    T = E.singleton(var("x"))
    thm = C.graphe_terme_valeur(X, T, "u", "x", "y")
    F = E.graphe_terme(X, T, "x")
    # {u∈X} ⊢ F(u) = {u}
    assert thm.conclusion == egal(E.valeur(F, u), E.singleton(u))
    assert thm.hypotheses == frozenset({appartient(u, X)})


def test_singleton_graphe_fonctionnel():
    thm = C.singleton_graphe_fonctionnel("X")
    assert thm.conclusion == E.est_fonctionnel(_G("X"))
    assert thm.est_clos


def test_singleton_graphe_domaine():
    thm = C.singleton_graphe_domaine("X")
    assert thm.conclusion == egal(E.dom(_G("X")), var("X"))
    assert thm.est_clos


def test_singleton_graphe_injective():
    thm = C.singleton_graphe_injective("X")
    assert thm.conclusion == E.injective_dans(_G("X"), var("X"))
    assert thm.est_clos


def test_singleton_inclus():
    u, X = var("u"), var("X")
    thm = C.singleton_inclus("u", "X")
    assert thm.conclusion == inclus(E.singleton(u), X)
    assert thm.hypotheses == frozenset({appartient(u, X)})


def test_singleton_dans_parties():
    u, X = var("u"), var("X")
    thm = C.singleton_dans_parties("u", "X")
    assert thm.conclusion == appartient(E.singleton(u), E.parties(X))
    assert thm.hypotheses == frozenset({appartient(u, X)})


def test_singleton_graphe_image_incluse():
    X = var("X")
    thm = C.singleton_graphe_image_incluse("X")
    assert thm.conclusion == inclus(E.image(_G("X"), X), E.parties(X))
    assert thm.est_clos


def test_inf_egal_parties():
    """⊢ X ≤ P(X)  (Cantor, étape 1) — la cible exacte inf_egal_card(X, P(X))."""
    X = var("X")
    thm = C.inf_egal_parties("X")
    assert thm.conclusion == inf_egal_card(X, E.parties(X))
    assert thm.est_clos


def test_paradoxe_diagonal():
    """⊢ ¬(P ⇔ ¬P) — cœur logique de l'argument diagonal (étape 2)."""
    P = appartient(var("a"), var("D"))
    thm = C.paradoxe_diagonal(P)
    assert thm.conclusion == non(equiv(P, non(P)))
    assert thm.est_clos


def test_aucune_surjection_parties():
    """{F bijection X→P(X)} ⊢ ¬(F bijection X→P(X)) — l'hypothèse se réfute."""
    X = var("X")
    bij = est_bijection_de(var("F"), X, E.parties(X))
    thm = C.aucune_surjection_parties("X", "F")
    assert thm.conclusion == non(bij)
    assert thm.hypotheses == frozenset({bij})


def test_cantor_non_equipotent():
    """⊢ ¬Eq(X, P(X)) — X n'est pas équipotent à son ensemble des parties."""
    X = var("X")
    thm = C.cantor_non_equipotent("X")
    assert thm.conclusion == non(equipotent(X, E.parties(X)))
    assert thm.est_clos


def test_cantor_distinct():
    """⊢ ¬(X = P(X))."""
    X = var("X")
    thm = C.cantor_distinct("X")
    assert thm.conclusion == non(egal(X, E.parties(X)))
    assert thm.est_clos


def test_cantor_strict():
    """⊢ X < P(X)  (THÉORÈME DE CANTOR : Card X < Card P(X), E.III.3)."""
    X = var("X")
    thm = C.cantor_strict("X")
    assert thm.conclusion == inf_strict_card(X, E.parties(X))
    assert thm.est_clos
