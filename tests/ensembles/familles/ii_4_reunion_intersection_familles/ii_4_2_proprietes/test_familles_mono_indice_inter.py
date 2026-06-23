"""Tests §II.4.2 — DÉCROISSANCE de l'intersection EN L'ENSEMBLE D'INDICES.

    J ⊂ I ⊢ ⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι       (`inter_incluse_sous_indices`)

Dual universel (∀) du patron `reunion_incluse_sous_indices`.  On vérifie :
conclusion EXACTE (== cible verbatim ET alpha_egal), théorème CLOS (hypothèse
J⊂I déchargée en implication → 0 hypothèse résiduelle), non-vacuité, et
theorie_ensembles() reste à 22 axiomes (aucun axiome neuf).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, impl, inclus, alpha_egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_2_proprietes.ensembles_familles_mono_indice_inter import (
    inter_incluse_sous_indices, cible)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_inter_incluse_sous_indices_conclusion():
    vf, vJ, vI = var("X"), var("J"), var("I")
    attendu = impl(inclus(vJ, vI),
                   inclus(E.inter_famille(vf, vI), E.inter_famille(vf, vJ)))
    t = inter_incluse_sous_indices()
    assert t.conclusion == attendu
    assert t.conclusion == cible()
    assert alpha_egal(t.conclusion, cible())


def test_inter_incluse_sous_indices_clos():
    t = inter_incluse_sous_indices()
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_non_vacuous():
    t = inter_incluse_sous_indices()
    assert t.conclusion not in t.hypotheses


def test_theorie_22_apres_construction():
    inter_incluse_sous_indices()
    assert len(E.theorie_ensembles().axiomes) == 22
