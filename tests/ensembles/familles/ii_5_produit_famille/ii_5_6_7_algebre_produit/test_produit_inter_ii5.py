"""§II.5 — commutation produit/intersection binaire :
   ∏(X_ι∩Y_ι) = (∏X_ι) ∩ (∏Y_ι)."""
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_6_7_algebre_produit import ensembles_produit_inter_ii5 as M
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def test_produit_inter_egal_inter_produits_close():
    th = M.produit_inter_egal_inter_produits()
    assert th.est_clos is True
    assert th.hypotheses == frozenset()
    assert th.conclusion == M._cible()
    # théorie inchangée
    assert len(E.theorie_ensembles().axiomes) == 22
