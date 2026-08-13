"""Tests §II.4 — ALGÈBRE des familles (bornes, monotonie-indice, f⁻¹⟨⋃⟩).

Vérifie pour chaque théorème : conclusion EXACTE (== cible verbatim),
.est_clos, et l'ABSENCE de vacuité (conclusion ∉ hypotheses).
theorie_ensembles() reste à 22 axiomes (aucun axiome neuf en théorie principale).
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, impl, appartient, existe,
                                       pourtout, inclus)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre import ensembles_familles_algebre as A
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_image_famille.ensembles_image_recip_famille_ii4 import (
    famille_image_recip as famille_reciproque)


def _non_vacuous(t):
    assert t.conclusion not in t.hypotheses


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_inter_incluse_terme():
    vf, vI, va = var("X"), var("I"), var("a")
    cible = impl(appartient(va, vI),
                 inclus(E.inter_famille(vf, vI), E.valeur_famille(vf, va)))
    t = A.inter_incluse_terme()
    assert t.est_clos
    assert t.conclusion == cible
    _non_vacuous(t)


def test_terme_inclus_reunion():
    vf, vI, va = var("X"), var("I"), var("a")
    cible = impl(appartient(va, vI),
                 inclus(E.valeur_famille(vf, va), E.reunion_famille(vf, vI)))
    t = A.terme_inclus_reunion()
    assert t.est_clos
    assert t.conclusion == cible
    _non_vacuous(t)


def test_inter_incluse_reunion():
    vf, vI, va = var("X"), var("I"), var("a")
    cible = impl(appartient(va, vI),
                 inclus(E.inter_famille(vf, vI), E.reunion_famille(vf, vI)))
    t = A.inter_incluse_reunion()
    assert t.est_clos
    assert t.conclusion == cible
    _non_vacuous(t)


def test_reunion_incluse_sous_indices():
    vf, vJ, vI = var("X"), var("J"), var("I")
    cible = impl(inclus(vJ, vI),
                 inclus(E.reunion_famille(vf, vJ), E.reunion_famille(vf, vI)))
    t = A.reunion_incluse_sous_indices()
    assert t.est_clos
    assert t.conclusion == cible
    _non_vacuous(t)


def test_image_reciproque_reunion_famille():
    vg, vfam, vI = var("f"), var("Y"), var("I")
    reun = E.reunion_famille(vfam, vI)
    fam_rec = famille_reciproque(vg, vfam)
    cible = egal(E.image(E.reciproque(vg), reun),
                 E.reunion_famille(fam_rec, vI))
    t = A.image_reciproque_reunion_famille()
    assert t.est_clos
    assert t.conclusion == cible
    _non_vacuous(t)
