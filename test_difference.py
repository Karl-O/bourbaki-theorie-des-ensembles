"""Tests V9 — différence E∖X et lois de De Morgan (binaires)."""
from __future__ import annotations

from formule import var, egal, et, non, appartient, equiv
from ensembles_abrege import difference, reunion, intersection
from ensembles_difference import de_morgan_reunion, de_morgan_inter
from tactiques_abrege2 import demorgan_ou, demorgan_et, et_ou_distrib


def test_demorgan_propositionnel():
    p, q = appartient(var("a"), var("A")), appartient(var("b"), var("B"))
    assert demorgan_ou(p, q).conclusion == equiv(non(__or(p, q)), et(non(p), non(q)))
    assert demorgan_et(p, q).conclusion == equiv(non(et(p, q)), __or(non(p), non(q)))
    assert demorgan_ou(p, q).est_clos and demorgan_et(p, q).est_clos


def __or(p, q):
    from formule import ou
    return ou(p, q)


def test_de_morgan_reunion():
    vE, vA, vB = var("E"), var("A"), var("B")
    t = de_morgan_reunion("E", "A", "B")
    cible = egal(difference(vE, reunion(vA, vB)),
                 intersection(difference(vE, vA), difference(vE, vB)))
    assert t.conclusion == cible and t.est_clos


def test_de_morgan_inter():
    vE, vA, vB = var("E"), var("A"), var("B")
    t = de_morgan_inter("E", "A", "B")
    cible = egal(difference(vE, intersection(vA, vB)),
                 reunion(difference(vE, vA), difference(vE, vB)))
    assert t.conclusion == cible and t.est_clos
