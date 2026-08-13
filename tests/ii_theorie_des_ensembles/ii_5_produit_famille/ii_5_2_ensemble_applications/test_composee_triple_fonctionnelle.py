"""Tests §II.5 Prop 2 (cœur) — fonctionnalité de la composée de trois fonctions."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_ensemble_applications.ensembles_composee_triple_fonctionnelle import (
    composee_triple_fonctionnelle, composee_triple_fonctionnelle_cible,
)


def test_composee_triple_fonctionnelle_close():
    t = composee_triple_fonctionnelle()
    assert t.est_clos is True
    assert len(t.hypotheses) == 0


def test_composee_triple_fonctionnelle_egale_cible():
    t = composee_triple_fonctionnelle()
    assert t.conclusion == composee_triple_fonctionnelle_cible()


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
