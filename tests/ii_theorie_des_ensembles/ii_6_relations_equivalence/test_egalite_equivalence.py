# -*- coding: utf-8 -*-
"""Tests Résumé §5, exemples d'équivalences : l'égalité (E.R.23 item 2, CLOS)
et la relation d'une partition (E.R.22 item 1 : symétrie CLOSE, réflexivité
modulo {H_rec, H_parties})."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, existe, appartient)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.ii_theorie_des_ensembles.ii_6_relations_equivalence.ensembles_egalite_equivalence import (
    egalite_est_equivalence, egalite_equivalence_enonce, classe_de_x_pour_egalite,
    relation_partition, recouvrement_points, parties_points,
    relation_partition_symetrique, relation_partition_reflexive_dans,
    relation_partition_reflexive_symetrique)


def test_clos():
    th = egalite_est_equivalence()
    assert th.conclusion == egalite_equivalence_enonce()
    assert not th.hypotheses


def test_enonce_est_le_predicat_du_depot():
    assert egalite_equivalence_enonce() == E.est_relation_equivalence(egal)


def test_classe_est_le_singleton():
    assert classe_de_x_pour_egalite("x") == E.singleton(var("x"))


# ── La relation d'une partition (E.R.22 item 1) ───────────────────────────────
def test_relation_partition_verbatim():
    """R{x,y} = (∃i)(i∈I et (x∈A_i et y∈A_i))  (verbatim du Résumé)."""
    vf, vI, vx, vy, vi = var("f"), var("I"), var("x"), var("y"), var("i")
    Ai = E.valeur_famille(vf, vi)
    rel = relation_partition(vf, vI)
    cible = existe("i", et(appartient(vi, vI),
                           et(appartient(vx, Ai), appartient(vy, Ai))))
    assert rel(vx, vy) == cible


def test_relation_partition_symetrique():
    """⊢ est_symetrique(R) — CLOS, cible exacte, 22 axiomes."""
    t = relation_partition_symetrique()
    rel = relation_partition(var("f"), var("I"))
    assert t.conclusion == E.est_symetrique(rel, "x", "y")
    assert t.est_clos
    assert t.hypotheses == frozenset()
    assert len(theorie_ensembles().axiomes) == 22


def test_relation_partition_reflexive_dans():
    """{H_rec, H_parties} ⊢ est_reflexive_dans(R, E) — hyps exactes."""
    t = relation_partition_reflexive_dans()
    vf, vI, vE = var("f"), var("I"), var("E")
    rel = relation_partition(vf, vI)
    assert t.conclusion == E.est_reflexive_dans(rel, vE, "x")
    assert t.hypotheses == frozenset({recouvrement_points(vf, vI, vE),
                                      parties_points(vf, vI, vE)})
    assert not t.est_clos
    assert len(theorie_ensembles().axiomes) == 22


def test_relation_partition_reflexive_symetrique():
    """Conjonction a) et b) — hyps = {H_rec, H_parties} uniquement."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et as et_f
    t = relation_partition_reflexive_symetrique()
    vf, vI, vE = var("f"), var("I"), var("E")
    rel = relation_partition(vf, vI)
    cible = et_f(E.est_reflexive_dans(rel, vE, "x"), E.est_symetrique(rel, "x", "y"))
    assert t.conclusion == cible
    assert t.hypotheses == frozenset({recouvrement_points(vf, vI, vE),
                                      parties_points(vf, vI, vE)})
