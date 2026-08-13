# -*- coding: utf-8 -*-
"""Test §III.5.8 — f(0) = 1 (0! = 1, E III.41 L.30).

t_fac_en_vide + restriction_vide_est_vide CLOS ; factorielle_zero sous les 6
hypothèses honnêtes (4 forme-du-livre + 2 données de position de 0).  theorie==22."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_zero import (
    t_fac_en_vide, restriction_vide_est_vide, factorielle_zero,
)

pytestmark = pytest.mark.slow


def test_t_fac_en_vide():
    """⊢ T_fac(∅) = 1 — CLOS (garde-disjonction + S7 + S5/existe_temoin)."""
    th = t_fac_en_vide()
    assert th.est_clos


def test_restriction_vide_est_vide():
    """⊢ F|∅ = ∅ — CLOS."""
    th = restriction_vide_est_vide(var("Fquelconque"))
    assert th.est_clos


def test_factorielle_zero():
    """🎯🎯 f(0)=1 sous 6 hypothèses honnêtes ; theorie==22."""
    th = factorielle_zero()
    assert len(th.hypotheses) == 6
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
