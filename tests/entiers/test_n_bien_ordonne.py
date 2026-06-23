"""Tests : ℕ est bien ordonné — est_bien_ordonne(R_ℕ, ℕ), CLOS, 0 hyp, theorie=22.

⚠️ LENT : appartenance_NN déclenche N_existe (~5 min, mémoïsé une fois par session).
"""
import pytest

from bourbaki.ensembles.ensembles_abrege import theorie_ensembles
from bourbaki.logique.formule import alpha_egal
import bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_n_bien_ordonne as M


def _n_axiomes():
    t = theorie_ensembles()
    return len(t.axiomes) if hasattr(t, "axiomes") else len(t)


def test_theorie_22():
    assert _n_axiomes() == 22


def test_relation_ordre_dans_NN_clos():
    t = M.relation_ordre_dans_NN()
    assert t.est_clos
    assert len(t.hypotheses) == 0


def test_clause_min_NN_clos():
    t = M.clause_min_NN()
    assert t.est_clos
    assert len(t.hypotheses) == 0


def test_n_bien_ordonne_CLOS():
    t = M.n_bien_ordonne()
    assert t.est_clos
    assert len(t.hypotheses) == 0


def test_n_bien_ordonne_EST_LA_CIBLE():
    t = M.n_bien_ordonne()
    # == est_bien_ordonne(R_ℕ, ℕ) à α-renommage près (liant τ interne d'est_cardinal)
    assert alpha_egal(t.conclusion, M.n_bien_ordonne_cible())


def test_non_vacuous():
    t = M.n_bien_ordonne()
    assert t.conclusion not in t.hypotheses


def test_theorie_22_apres():
    M.n_bien_ordonne()
    assert _n_axiomes() == 22
