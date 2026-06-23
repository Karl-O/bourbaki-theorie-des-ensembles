"""Tests — §III.6.3 surjectivité/domaine couple-natifs du recollement de chaîne."""
from bourbaki.cardinaux.ensembles_chaine_surjective_frame import (
    recollement_surjectif, recollement_domaine,
    union_chaine_surjective, union_chaine_dom,
)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def _theorie22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_union_chaine_surjective():
    s = union_chaine_surjective()
    assert recollement_surjectif(E.var("Dchaine"), E.var("USchaine")) in s.hypotheses
    assert s.conclusion not in s.hypotheses
    assert len(s.hypotheses) == 1
    _theorie22()


def test_union_chaine_dom():
    d = union_chaine_dom()
    assert recollement_domaine(E.var("Dchaine"), E.var("Domchaine")) in d.hypotheses
    assert d.conclusion not in d.hypotheses
    assert len(d.hypotheses) == 1
    _theorie22()


def test_theorie_inchangee():
    _theorie22()
