"""Tests §II.5 Prop.10 (sens direct) : monotonie du produit ∏Xⱼ ⊂ ∏Yⱼ."""
from bourbaki.ensembles.familles import ensembles_produit_monotone_ii5 as M
from bourbaki.ensembles import ensembles_abrege as E


def test_produit_monotone_close():
    t = M.produit_monotone()
    assert t.est_clos is True
    assert t.hypotheses == frozenset()
    assert t.conclusion == M._cible()


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
