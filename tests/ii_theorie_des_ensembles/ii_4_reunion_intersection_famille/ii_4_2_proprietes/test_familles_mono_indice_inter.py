"""Tests §II.4.2 — DÉCROISSANCE de l'intersection EN L'ENSEMBLE D'INDICES.

    (J ⊂ I) ⇒ ( (∃i)(i∈J) ⇒ ⋂_{ι∈I} X_ι ⊂ ⋂_{ι∈J} X_ι )
                                                (`inter_incluse_sous_indices`)

Dual universel (∀) du patron `reunion_incluse_sous_indices`.  On vérifie :
conclusion EXACTE (== cible verbatim ET alpha_egal), théorème CLOS (hypothèses
J⊂I et J≠∅ déchargées en implications → 0 hypothèse résiduelle), non-vacuité, et
theorie_ensembles() reste à 22 axiomes (aucun axiome neuf).

⚠ ÉNONCÉ RENFORCÉ (migration de la Déf. 2 vers ⋂ = SÉLECTION dans ⋃).  Ce test
attendait auparavant la forme SANS hypothèse « (J⊂I) ⇒ ⋂_I ⊂ ⋂_J ».  Cette forme
est FAUSSE pour J = ∅ (⋂_{ι∈∅} X_ι = ∅ tandis que ⋂_I peut être non vide) : elle
n'était démontrable que par l'ancien AXIOME_INTER_FAM, qui était contradictoire.
Le test suit donc l'énoncé corrigé, qui porte l'hypothèse (∃i)(i∈J) écrite par
Bourbaki dans la Déf. 2 (E II.22, « … dont l'ensemble d'indices n'est pas vide »).
On vérifie EN PLUS ci-dessous que l'hypothèse est bien présente et porte sur J
(et non sur I : (∃i)(i∈I) ne suffirait pas).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, impl, inclus, alpha_egal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    indices_non_vides)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_2_proprietes.ensembles_familles_mono_indice_inter import (
    inter_incluse_sous_indices, cible)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_inter_incluse_sous_indices_conclusion():
    vf, vJ, vI = var("X"), var("J"), var("I")
    attendu = impl(inclus(vJ, vI),
                   impl(indices_non_vides(vJ),
                        inclus(E.inter_famille(vf, vI), E.inter_famille(vf, vJ))))
    t = inter_incluse_sous_indices()
    assert t.conclusion == attendu
    assert t.conclusion == cible()
    assert alpha_egal(t.conclusion, cible())


def test_hypothese_non_vide_porte_sur_J():
    """L'hypothèse ajoutée est (∃i)(i∈J) — sur le PETIT ensemble d'indices.

    (∃i)(i∈I) ne suffirait pas : J=∅ ⊂ I≠∅ met l'inclusion en défaut.  On ancre
    ce point pour qu'un affaiblissement accidentel (I à la place de J) échoue."""
    vJ, vI = var("J"), var("I")
    t = inter_incluse_sous_indices()
    assert t.conclusion == impl(inclus(vJ, vI),
                                impl(indices_non_vides(vJ),
                                     inclus(E.inter_famille(var("X"), vI),
                                            E.inter_famille(var("X"), vJ))))
    assert indices_non_vides(vJ) != indices_non_vides(vI)


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
