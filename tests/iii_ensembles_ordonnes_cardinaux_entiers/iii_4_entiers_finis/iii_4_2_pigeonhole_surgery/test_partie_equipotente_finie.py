"""Tests — §III.4-5 pigeonhole forme équipotente (partie_equipotente_egale)."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_2_pigeonhole_surgery.ensembles_partie_equipotente_finie import (
    partie_equipotente_egale, partie_equipotente_egale_enonce,
)
import pytest

#: FICHIER LOURD — 731 s mesurés le 18 août (pytest --durations).
#: Marqué slow : la porte « not slow » ne le voit plus, mais le théorème
#: reste vérifié par la suite COMPLÈTE — à lancer avant toute annonce.
pytestmark = pytest.mark.slow


def test_partie_equipotente_egale_close():
    r = partie_equipotente_egale()
    assert r.est_clos
    assert not r.hypotheses
    assert r.conclusion == partie_equipotente_egale_enonce()


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
