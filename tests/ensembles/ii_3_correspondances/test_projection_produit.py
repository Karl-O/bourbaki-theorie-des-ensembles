"""Tests §II.3 — Projections d'un produit : pr₁⟨X×Y⟩=X (Y≠∅), pr₂⟨X×Y⟩=Y (X≠∅)."""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_3_correspondances.ensembles_projection_produit import (
    pr1_produit, pr2_produit, cible_pr1_produit, cible_pr2_produit)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pr1_produit_close():
    """⊢ (∃e)(e∈Y) ⇒ dom(X×Y) = X."""
    th = pr1_produit()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible_pr1_produit()


def test_pr2_produit_close():
    """⊢ (∃e)(e∈X) ⇒ img(X×Y) = Y."""
    th = pr2_produit()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible_pr2_produit()


def test_projection_produit_parametrable():
    th = pr1_produit("A", "B")
    assert th.est_clos
    assert th.conclusion == cible_pr1_produit("A", "B")
    assert len(E.theorie_ensembles().axiomes) == 22
