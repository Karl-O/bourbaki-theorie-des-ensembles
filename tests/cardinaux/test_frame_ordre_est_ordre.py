"""Tests — Γ𝔉(E) est un ORDRE sur 𝔉(E) (Hessenberg, Zorn E.III.48)."""
from bourbaki.logique.formule import var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    reflexivite_sur, antisymetrie, transitivite_rel, est_ordre,
)
from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair, frame_ordre
from bourbaki.cardinaux.ensembles_frame_ordre_est_ordre import (
    frame_ordre_reflexive, frame_ordre_antisymetrique, frame_ordre_transitive,
    frame_ordre_est_ordre,
)


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def _Gam():
    return frame_ordre(var("E"))


def _Fr():
    return frame_pair(var("E"))


def test_reflexive():
    thm = frame_ordre_reflexive()
    assert thm.est_clos
    assert thm.conclusion == reflexivite_sur(_Gam(), _Fr(), "p")


def test_antisymetrique():
    thm = frame_ordre_antisymetrique()
    assert thm.est_clos
    assert thm.conclusion == antisymetrie(_Gam(), "p", "q")


def test_transitive():
    thm = frame_ordre_transitive()
    assert thm.est_clos
    assert thm.conclusion == transitivite_rel(_Gam(), "p", "q", "r")


def test_est_ordre():
    thm = frame_ordre_est_ordre()
    assert thm.est_clos
    assert thm.conclusion == est_ordre(_Gam(), _Fr(), "p", "q", "r")
