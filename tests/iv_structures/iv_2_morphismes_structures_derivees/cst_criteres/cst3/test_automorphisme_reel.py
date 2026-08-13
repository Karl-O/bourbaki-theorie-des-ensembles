# -*- coding: utf-8 -*-
"""Tests — automorphisme-identité réel + auto-isomorphie (IV.1.5)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    schema_relation,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_automorphisme_identite_reel import (
    automorphisme_identite_reel, sont_isomorphes_reel,
)


def test_automorphisme_identite_reel():
    """1 seule hyp (U∈S(E)) — bijectivité T5 CLOSE + valeur CST1-id."""
    th = automorphisme_identite_reel(schema_relation(), ["Eb1"])
    assert len(th.hypotheses) == 1


def test_sont_isomorphes_reel():
    """(S(E),U) isomorphe à lui-même — témoin ⟨Δ⟩^S ; theorie==22."""
    th = sont_isomorphes_reel(schema_relation(), ["Eb1"])
    assert len(th.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22
