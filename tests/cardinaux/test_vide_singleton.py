"""Tests §III.3 — LEMME FONDATEUR « 0 ≠ 1 » :  ⊢ ¬ Eq(∅, {∅}).

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et est_clos.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, non
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_vide_singleton as VS
from bourbaki.cardinaux.ensembles_cardinaux import equipotent


def test_image_sur_vide():
    """⊢ image(F, ∅) = ∅."""
    thm = VS.image_sur_vide("F")
    assert thm.conclusion == egal(E.image(var("F"), E.VIDE), E.VIDE)
    assert thm.est_clos


def test_image_sur_vide_autre_graphe():
    """⊢ image(G, ∅) = ∅  (graphe quelconque : la preuve ne dépend pas du nom)."""
    thm = VS.image_sur_vide("G")
    assert thm.conclusion == egal(E.image(var("G"), E.VIDE), E.VIDE)
    assert thm.est_clos


def test_vide_distinct_singleton():
    """⊢ ¬(∅ = {∅})."""
    thm = VS.vide_distinct_singleton()
    assert thm.conclusion == non(egal(E.VIDE, E.singleton(E.VIDE)))
    assert thm.est_clos


def test_vide_non_equipotent_singleton():
    """⊢ ¬ Eq(∅, {∅})  (le théorème fondateur 0 ≠ 1)."""
    thm = VS.vide_non_equipotent_singleton()
    assert thm.conclusion == non(equipotent(E.VIDE, E.singleton(E.VIDE)))
    assert thm.est_clos
