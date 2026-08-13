"""Goldbach borné SUR n — l'énoncé de la conjecture, restreint par UN conjoint.

La forme en k parlait des moitiés ; celle-ci parle de n.  Le test central est la
FIDÉLITÉ : l'antécédent et le conséquent sont PRÉLEVÉS sur goldbach() (découpe
par .sous puis recomposition vérifiée), jamais recopiés.
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    impl, pourtout,
)
from outils_ia.conjectures import goldbach as GB
from outils_ia.conjectures.goldbach_borne_n import (
    antecedent, cible, conjoints, decoupe_goldbach, fidelite_verifiee,
    goldbach_borne_n,
)


def test_le_prelevement_recompose_goldbach():
    """🔴 GARDE DE FIDÉLITÉ — le découpage doit redonner goldbach() à l'identique."""
    nom, ANTE, DEC = decoupe_goldbach()          # un TRIPLET : le lieur d'abord
    assert pourtout(nom, impl(ANTE, DEC)) == GB.goldbach()
    assert fidelite_verifiee()


def test_l_antecedent_borne_est_l_antecedent_plus_la_borne():
    """cible(B) = goldbach() dont l'antécédent porte UN conjoint de plus."""
    nom, ANTE, DEC = decoupe_goldbach()
    for B in (6, 10):
        assert cible(B) == pourtout(nom, impl(antecedent(B), DEC))
        assert len(conjoints(B)) == 5      # Fini, pair, ≠0, ≠2, ≤N(B)


@pytest.mark.slow
def test_goldbach_sur_n_jusqu_a_dix():
    """⊢ la conjecture restreinte à n ≤ 10 — CLOS, 0 hypothèse (~70 s à froid)."""
    th = goldbach_borne_n(6)
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == cible(6)
    th10 = goldbach_borne_n(10)
    assert th10.est_clos and th10.conclusion == cible(10)
    assert len(E.theorie_ensembles().axiomes) == 22
