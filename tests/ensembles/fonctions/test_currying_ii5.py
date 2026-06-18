"""Tests §II.5 — Proposition 3 (currying ensembliste) et Proposition 2."""
from bourbaki.ensembles import ensembles_abrege as E
import bourbaki.cardinaux.ensembles_cardinaux as C
from bourbaki.ensembles.fonctions.ensembles_currying_ii5 import (
    prop3_currying_bijection, source, but)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop3_currying_bijection_close():
    th = prop3_currying_bijection()
    assert th.est_clos
    assert len(th.hypotheses) == 0


def test_prop3_conclusion_est_equipotent():
    """La conclusion est LITTÉRALEMENT equipotent(𝓕(B×C;A), 𝓕(C;𝓕(B;A)))
    = (∃F) est_bijection_de(F, 𝓕(B×C;A), 𝓕(C;𝓕(B;A))) (Prop 3 §5)."""
    th = prop3_currying_bijection()
    assert th.conclusion == C.equipotent(source(), but())
    # theorie inchangée APRÈS construction
    assert len(E.theorie_ensembles().axiomes) == 22
