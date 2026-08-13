"""Test Résumé §3.3e — pr₁⁻¹(X) = X×F  (image réciproque d'une projection, X⊂E).

APPEL du théorème, conclusion == cible Bourbaki reconstruite, clôture (0 hyp),
theorie_ensembles()==22.
"""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_2_reciproque.ensembles_projection_reciproque_produit import (
    pr1_reciproque_produit, cible_pr1_reciproque_produit)


def test_theorie_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pr1_reciproque_produit():
    """⊢ X⊂E ⇒ image(reciproque(graphe_terme(E×F,pr₁(k),'k')), X) = X×F."""
    th = pr1_reciproque_produit()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible_pr1_reciproque_produit()
    assert len(E.theorie_ensembles().axiomes) == 22
