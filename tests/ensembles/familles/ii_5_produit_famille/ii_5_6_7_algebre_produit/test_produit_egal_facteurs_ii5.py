"""Test §II.5 — ∏ à facteurs égaux ⇒ produits égaux (corollaire Prop.10)."""
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_6_7_algebre_produit import ensembles_produit_egal_facteurs_ii5 as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def test_produit_egal_si_facteurs_egaux_close():
    th = M.produit_egal_si_facteurs_egaux()
    assert th.est_clos is True
    assert list(th.hypotheses) == []
    assert th.conclusion == M._cible()
    assert len(E.theorie_ensembles().axiomes) == 22
