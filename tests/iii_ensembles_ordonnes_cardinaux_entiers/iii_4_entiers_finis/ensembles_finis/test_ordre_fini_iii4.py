"""Tests §III.4 — Prop 3 (variante totalement ordonnée) et Cor 1."""
import pytest

from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.ensembles_finis.ensembles_ordre_fini_iii4 import (
    prop3_total, prop3_total_enonce,
    cor1_total, cor1_total_enonce,
    prop3_filtrant, prop3_filtrant_enonce,
    _membre_union_singleton,
    cor2_maximal, cor2_enonce,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_membre_union_singleton_clos():
    t = _membre_union_singleton("z", "X", "x")
    assert t.est_clos


def test_prop3_total_clos():
    r = prop3_total()
    assert r.est_clos, f"hyps résiduelles : {r.hypotheses}"
    assert r.conclusion == prop3_total_enonce("Gpgt", "Epgt", "Xpgt", "m_pgf")


def test_cor1_total_clos():
    r = cor1_total()
    assert r.est_clos, f"hyps résiduelles : {r.hypotheses}"
    assert r.conclusion == cor1_total_enonce("Gpgt", "Epgt", "m_pgf")


def test_prop3_filtrant_clos():
    r = prop3_filtrant()
    assert r.est_clos, f"hyps résiduelles : {r.hypotheses}"
    assert r.conclusion == prop3_filtrant_enonce("Gmjt", "Emjt", "Xmjt", "m_mjf")


def test_cor2_maximal_clos():
    r = cor2_maximal()
    assert r.est_clos, f"hyps résiduelles : {r.hypotheses}"
    assert r.conclusion == cor2_enonce("Gemf", "Eemf", "m_emf")
