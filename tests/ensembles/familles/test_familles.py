"""Tests §II.4 — réunion et intersection d'une famille d'ensembles.

Vérifie la conclusion EXACTE (== cible) et .est_clos de chaque théorème certifié.
"""
from bourbaki.logique.formule import (var, egal, et, impl, appartient, existe, pourtout, inclus, equiv)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_1_definitions_algebre import ensembles_familles as F


def test_membre_reunion_famille():
    vf, vI, vz, vi = var("f"), var("I"), var("z"), var("i")
    cible = equiv(appartient(vz, E.reunion_famille(vf, vI)),
                  existe("i", et(appartient(vi, vI),
                                 appartient(vz, E.valeur_famille(vf, vi)))))
    t = F.membre_reunion_famille()
    assert t.est_clos
    assert t.conclusion == cible


def test_membre_inter_famille():
    vf, vI, vz, vi = var("f"), var("I"), var("z"), var("i")
    cible = equiv(appartient(vz, E.inter_famille(vf, vI)),
                  pourtout("i", impl(appartient(vi, vI),
                                     appartient(vz, E.valeur_famille(vf, vi)))))
    t = F.membre_inter_famille()
    assert t.est_clos
    assert t.conclusion == cible


def test_reunion_famille_intro():
    vf, vI, va, vz = var("f"), var("I"), var("a"), var("z")
    cible = impl(et(appartient(va, vI), appartient(vz, E.valeur_famille(vf, va))),
                 appartient(vz, E.reunion_famille(vf, vI)))
    t = F.reunion_famille_intro()
    assert t.est_clos
    assert t.conclusion == cible


def test_inter_famille_elim():
    vf, vI, va, vz = var("f"), var("I"), var("a"), var("z")
    cible = impl(appartient(vz, E.inter_famille(vf, vI)),
                 impl(appartient(va, vI), appartient(vz, E.valeur_famille(vf, va))))
    t = F.inter_famille_elim()
    assert t.est_clos
    assert t.conclusion == cible


def test_monotonie_reunion_famille():
    vf, vg, vI, vi = var("f"), var("g"), var("I"), var("i")
    hyp = pourtout("i", inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)))
    cible = impl(hyp, inclus(E.reunion_famille(vf, vI), E.reunion_famille(vg, vI)))
    t = F.monotonie_reunion_famille()
    assert t.est_clos
    assert t.conclusion == cible


def test_monotonie_inter_famille():
    vf, vg, vI, vi = var("f"), var("g"), var("I"), var("i")
    hyp = pourtout("i", inclus(E.valeur_famille(vf, vi), E.valeur_famille(vg, vi)))
    cible = impl(hyp, inclus(E.inter_famille(vf, vI), E.inter_famille(vg, vI)))
    t = F.monotonie_inter_famille()
    assert t.est_clos
    assert t.conclusion == cible


def test_reunion_famille_vide():
    vf = var("f")
    cible = egal(E.reunion_famille(vf, E.VIDE), E.VIDE)
    t = F.reunion_famille_vide()
    assert t.est_clos
    assert t.conclusion == cible


def test_axiomes_familles_dans_theorie():
    th = E.theorie_ensembles()
    assert E.AXIOME_REUNION_FAM in th.axiomes
    assert E.AXIOME_INTER_FAM in th.axiomes
