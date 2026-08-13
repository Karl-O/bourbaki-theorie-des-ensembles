# -*- coding: utf-8 -*-
"""Tests §I.2.4 — théorie plus forte, théories équivalentes (E I.24)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, implication)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.i_2_2_demonstration import (
    est_theoreme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.i_2_4_comparaison_theories import (
    est_plus_forte, sont_equivalentes)

A, B = Assemblage(("A",)), Assemblage(("B",))
SIGNES, SCHEMAS = {"∈"}, {"S1", "S2", "S3", "S4"}


def _certificat(axiomes):
    """est_theoreme_p par démonstration couche 0 : ici, les axiomes eux-mêmes
    et ce qui s'en déduit par détachement."""
    def check(r):
        return est_theoreme(r, tuple(axiomes) + (r,), axiomes) or r in axiomes
    return check


def test_plus_forte_extension_d_axiomes():
    """𝒯' = 𝒯 + un axiome de plus est plus forte que 𝒯 (mêmes signes/schémas)."""
    ax_t = (A,)
    ax_tp = (A, implication(A, B))
    assert est_plus_forte(SIGNES, SCHEMAS, ax_t, SIGNES, SCHEMAS, _certificat(ax_tp))
    # et pas l'inverse : A⇒B n'est pas un théorème de {A} au fragment couche 0
    assert not est_plus_forte(SIGNES, SCHEMAS, ax_tp, SIGNES, SCHEMAS, _certificat(ax_t))


def test_plus_forte_exige_les_signes():
    assert not est_plus_forte({"∈", "="}, SCHEMAS, (A,), {"∈"}, SCHEMAS, lambda r: True)


def test_equivalentes_presentations_differentes():
    """Deux présentations avec les mêmes axiomes (ordres différents) sont équivalentes."""
    ax1, ax2 = (A, B), (B, A)
    assert sont_equivalentes(SIGNES, SCHEMAS, ax1, _certificat(ax2),
                             SIGNES, SCHEMAS, ax2, _certificat(ax1))
