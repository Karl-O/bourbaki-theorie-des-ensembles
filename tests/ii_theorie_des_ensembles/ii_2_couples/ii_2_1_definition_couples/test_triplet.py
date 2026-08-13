"""Tests §II.2 — Triplet (a,b,c)=((a,b),c) et ses trois projections (Résumé §3 item 12)."""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_triplet import (
    triplet_projection_1, triplet_projection_2, triplet_projection_3,
    cible_triplet_projection_1, cible_triplet_projection_2, cible_triplet_projection_3)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_triplet_projection_1_close():
    th = triplet_projection_1()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible_triplet_projection_1()   # pr₁³((a,b,c)) = a


def test_triplet_projection_2_close():
    th = triplet_projection_2()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible_triplet_projection_2()   # pr₂³((a,b,c)) = b


def test_triplet_projection_3_close():
    th = triplet_projection_3()
    assert th.est_clos and len(th.hypotheses) == 0
    assert th.conclusion == cible_triplet_projection_3()   # pr₃³((a,b,c)) = c


def test_triplet_projections_parametrables():
    """Composantes libres arbitraires (distinctes de x, y, liants de pr₁/pr₂)."""
    for f, c in [(triplet_projection_1, cible_triplet_projection_1),
                 (triplet_projection_2, cible_triplet_projection_2),
                 (triplet_projection_3, cible_triplet_projection_3)]:
        th = f("p", "q", "r")
        assert th.est_clos
        assert th.conclusion == c("p", "q", "r")
    assert len(E.theorie_ensembles().axiomes) == 22
