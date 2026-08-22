# -*- coding: utf-8 -*-
"""Tests §III.6 (Lemme 2) — W5 : injectivité du couplage (m,n) ↦ 2^m·3^n."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_pairing import (
    pairing_injectif, pairing_injectif_cible,
)


def test_pairing_injectif():
    """🎯 W5 : ⊢ (Fini m,mp,n,np ∧ 2^m·3^n = 2^mp·3^np) ⇒ (m=mp ∧ n=np)."""
    r = pairing_injectif()
    assert not r.hypotheses
    assert r.conclusion == pairing_injectif_cible()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
