"""Tests §II.5 Prop 2 (cœur) — fonctionnalité de la composée de trois fonctions."""
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_composee_triple_fonctionnelle import (
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
