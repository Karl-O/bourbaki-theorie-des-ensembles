# -*- coding: utf-8 -*-
"""Test §III.3.3 Prop.5 c) niveau OPÉRATIONS — a·(b+c) = a·b + a·c, CLOS.

La brique-pont désignée par le marcheur (EXP6, 21 août 2026) : les opérations
cardinales prennent le Card de leurs arguments, le théorème ensembliste
travaille sur les ensembles nus — le respect de l'équipotence fait le pont.
"""
import pytest

import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E

pytestmark = pytest.mark.slow


def test_distributivite_operations():
    """⊢ PCB(a, SC(b,c)) = SC(PCB(a,b), PCB(a,c)), clos, énoncé asserté."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_distributivite_operations import (
        distributivite_operations, enonce_distributivite_operations)
    r = distributivite_operations()
    assert r.est_clos and not r.hypotheses
    assert r.conclusion == enonce_distributivite_operations()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
