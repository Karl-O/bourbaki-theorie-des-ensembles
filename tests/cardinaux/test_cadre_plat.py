"""Tests du CADRE PLAT (déverrouillage hyp[2] de Hessenberg a²=a)."""
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.formule import var
import bourbaki.cardinaux.ensembles_cadre_plat as m


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_P1_blocs_disjoints():
    """P1 : les 3 blocs plats deux à deux disjoints + bloc-tête, sous U∩S₀=∅."""
    t = m.cadre_plat_blocs_disjoints()
    cible = m.cadre_plat_blocs_disjoints_cible()
    # conclusion == conséquent de la cible
    assert t.conclusion == cible.sous[1]
    # une seule hypothèse honnête : U∩S₀=∅
    assert len(t.hypotheses) == 1
    assert E.sont_disjoints(var("Ucadre"), var("S0")) in t.hypotheses
    # non vacueux
    assert t.conclusion not in t.hypotheses
