"""Tests §II.4 Prop. 1 dual (intersection) — reparamétrage surjectif."""
from bourbaki.ensembles.familles import ensembles_reparam_inter_ii4 as M
from bourbaki.ensembles import ensembles_abrege as E


def test_reparam_inter_egal_clos_et_cible():
    th = M.reparam_inter_egal_si_surjectif()
    assert th.est_clos
    assert th.conclusion == M._cible()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_reparam_inter_incluse_close():
    th = M.reparam_inter_incluse()
    assert th.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22
