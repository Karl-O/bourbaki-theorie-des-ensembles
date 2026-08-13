# -*- coding: utf-8 -*-
"""Tests — l'ENCODAGE de la somme indexée (P0 de S3, §II.4.8 Déf. 8).

L'axiome de définition vit dans la théorie DÉDIÉE theorie_somme_famille() ;
theorie_ensembles() reste à 22 axiomes (l'invariant du projet)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, equiv, appartient, existe)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_indexee import (
    AXIOME_SOMME_FAM, theorie_somme_famille, membre_somme_famille,
    element_marque_dans_somme)


def test_theorie_22():
    """L'axiome-somme est DÉDIÉ : les 22 axiomes de la théorie sont intacts."""
    assert len(E.theorie_ensembles().axiomes) == 22
    assert AXIOME_SOMME_FAM not in E.theorie_ensembles().axiomes
    assert theorie_somme_famille().axiomes == [AXIOME_SOMME_FAM]


def test_p0_membre_somme_famille():
    """⊢ (z∈⊔(f,I)) ⇔ (∃i)((i∈I) et (z ∈ X_i×{i})) — instance close, forme exacte."""
    vfam, vI, vz = var("Afq"), var("Ifq"), var("zfq")
    thm = membre_somme_famille(vfam, vI, vz)
    assert thm.est_clos
    vi = var("i")
    corps = et(appartient(vi, vI),
               appartient(vz, E.produit(E.valeur_famille(vfam, vi),
                                        E.singleton(vi))))
    assert thm.conclusion == equiv(appartient(vz, E.somme_famille(vfam, vI)),
                                   existe("i", corps))


def test_p0_element_marque_dans_somme():
    """{i0∈I, u∈X_{i0}} ⊢ (u,i0)∈⊔ — l'injection canonique brute, 2 hyps."""
    vfam, vI, vu, vi = var("Afq"), var("Ifq"), var("ufq"), var("i0fq")
    thm = element_marque_dans_somme(vfam, vI, vu, vi)
    assert thm.conclusion == appartient(E.couple(vu, vi),
                                        E.somme_famille(vfam, vI))
    assert thm.hypotheses == frozenset({
        appartient(vi, vI),
        appartient(vu, E.valeur_famille(vfam, vi))})
    assert len(E.theorie_ensembles().axiomes) == 22
