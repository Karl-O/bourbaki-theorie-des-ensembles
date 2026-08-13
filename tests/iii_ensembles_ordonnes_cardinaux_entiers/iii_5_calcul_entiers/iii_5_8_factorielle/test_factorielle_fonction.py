# -*- coding: utf-8 -*-
"""Test §III.5.8 — LA FONCTION FACTORIELLE EXISTE (C62 assemblé, règle T_fac).

⊢ (∃f)( est_fonctionnel(f) ∧ dom(f)=ℕ ∧ (∀n∈ℕ)( f(n)=T_fac(n) ) )
sous les 3 résidus C62.  theorie==22."""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_fonction import (
    factorielle_fonction_cible, factorielle_fonction_existe,
    factorielle_equation_restriction,
)

pytestmark = pytest.mark.slow


def test_factorielle_equation_restriction():
    """🎯🎯 LA FORME DU LIVRE : (∀n∈ℕ) f(n) = T_fac(f|seg(n)) — 4 hyps honnêtes."""
    th = factorielle_equation_restriction()
    assert len(th.hypotheses) == 4
    assert th.conclusion not in th.hypotheses


def test_factorielle_fonction_existe():
    """🎯🎯 La fonction factorielle (récurrence C62) existe — 3 hyps honnêtes."""
    th = factorielle_fonction_existe()
    assert th.conclusion == factorielle_fonction_cible()
    assert th.conclusion.tag == "exists"
    assert len(th.hypotheses) == 3
    assert th.conclusion not in th.hypotheses


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22
