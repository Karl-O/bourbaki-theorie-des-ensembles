"""Tests — §III.5.2 soustraction des entiers (Cor. 4 Prop. 3, E.III.37)."""
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import (
    existe_complement_somme, existe_complement_somme_enonce,
    soustraction_caracterisation, soustraction_caracterisation_enonce,
    soustraction_unicite, soustraction_unicite_enonce,
)
from bourbaki.ensembles.ensembles_abrege import theorie_ensembles


def test_existence_clos():
    t = existe_complement_somme("a", "b")
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == existe_complement_somme_enonce("a", "b")


def test_caracterisation_clos():
    t = soustraction_caracterisation("a", "b")
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == soustraction_caracterisation_enonce("a", "b")


def test_unicite_clos():
    t = soustraction_unicite("a", "c", "cp", "b")
    assert t.est_clos and not t.hypotheses
    assert t.conclusion == soustraction_unicite_enonce("a", "c", "cp", "b")


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
