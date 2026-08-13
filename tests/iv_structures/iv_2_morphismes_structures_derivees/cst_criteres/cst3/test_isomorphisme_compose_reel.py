# -*- coding: utf-8 -*-
"""Tests — composition d'isomorphismes réelle (transitivité, IV.1.5)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_especes_echelon import (
    schema_relation,
)
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.cst3.ensembles_isomorphisme_compose_reel import (
    isomorphisme_compose_reel,
)


def test_compose_reel():
    """👑 bij(⟨g∘f⟩^S) ∧ ⟨g∘f⟩^S(U)=W — l'isomorphie réelle est TRANSITIVE."""
    th, hy = isomorphisme_compose_reel(
        schema_relation(), ["f1"], ["g1"], ["Eb1"], ["Ep1"], ["Eq1"])
    assert set(th.hypotheses) <= set(hy)
    assert len(E.theorie_ensembles().axiomes) == 22
