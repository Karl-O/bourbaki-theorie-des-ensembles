"""Tests — GAP B : transport d'un sous-ensemble réalisant un cardinal DANS A."""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_transport_sous_ensemble import (
    existe_sous_ensemble_cardinal_transporte,
    existe_sous_ensemble_cardinal_transporte_cible,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_transport_clos_inconditionnel():
    thm = existe_sous_ensemble_cardinal_transporte()
    assert thm.est_clos
    assert list(thm.hypotheses) == []
    assert thm.conclusion == existe_sous_ensemble_cardinal_transporte_cible()
    assert thm.conclusion not in thm.hypotheses
