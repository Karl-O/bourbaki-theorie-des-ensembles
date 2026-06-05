"""Tests V9 — §II.6 Relations d'équivalence.

Vérifient la conclusion EXACTE (== cible) et la clôture (.est_clos / hypothèses
attendues) de chaque théorème certifié par le noyau abrégé.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, impl, equiv, appartient, pourtout, existe,
                     afficher_f)
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux import ensembles_equivalence as Q


# ── Définitions (formules verbatim) ───────────────────────────────────────────
def test_est_symetrique_def():
    R = E.rel_graphe("G")
    vx, vy = var("x"), var("y")
    assert E.est_symetrique(R) == pourtout("x", pourtout("y", impl(R(vx, vy), R(vy, vx))))


def test_est_transitive_def():
    R = E.rel_graphe("G")
    vx, vy, vz = var("x"), var("y"), var("z")
    assert E.est_transitive(R) == pourtout("x", pourtout("y", pourtout("z",
        impl(et(R(vx, vy), R(vy, vz)), R(vx, vz)))))


def test_est_relation_equivalence_def():
    R = E.rel_graphe("G")
    assert E.est_relation_equivalence(R) == et(E.est_symetrique(R), E.est_transitive(R))


def test_est_reflexive_dans_def():
    R = E.rel_graphe("G")
    vx = var("x")
    assert E.est_reflexive_dans(R, var("E")) == pourtout("x",
        equiv(R(vx, vx), appartient(vx, var("E"))))


def test_classe_est_image_singleton():
    assert E.classe(var("G"), var("a")) == E.image(var("G"), E.singleton(var("a")))


# ── Théorèmes ─────────────────────────────────────────────────────────────────
def test_equivalence_reflexive_gauche():
    R = E.rel_graphe("G")
    vx, vy = var("x"), var("y")
    t = Q.equivalence_reflexive_gauche()
    assert t.conclusion == impl(R(vx, vy), R(vx, vx))
    assert not t.est_clos
    assert t.hypotheses == frozenset({E.est_symetrique(R), E.est_transitive(R)})


def test_equivalence_reflexive_droite():
    R = E.rel_graphe("G")
    vx, vy = var("x"), var("y")
    t = Q.equivalence_reflexive_droite()
    assert t.conclusion == impl(R(vx, vy), R(vy, vy))
    assert t.hypotheses == frozenset({E.est_symetrique(R), E.est_transitive(R)})


def test_equivalence_reflexive():
    R = E.rel_graphe("G")
    vx, vy = var("x"), var("y")
    t = Q.equivalence_reflexive()
    assert t.conclusion == impl(R(vx, vy), et(R(vx, vx), R(vy, vy)))
    assert t.hypotheses == frozenset({E.est_symetrique(R), E.est_transitive(R)})


def test_symetrie_relation():
    R = E.rel_graphe("G")
    vx, vy = var("x"), var("y")
    t = Q.symetrie_relation()
    assert t.conclusion == impl(R(vx, vy), R(vy, vx))
    assert t.hypotheses == frozenset({E.est_symetrique(R)})


def test_transitivite_relation():
    R = E.rel_graphe("G")
    vx, vy, vz = var("x"), var("y"), var("z")
    t = Q.transitivite_relation()
    assert t.conclusion == impl(et(R(vx, vy), R(vy, vz)), R(vx, vz))
    assert t.hypotheses == frozenset({E.est_transitive(R)})


def test_classe_membre():
    vG, va, vy = var("G"), var("a"), var("y")
    t = Q.classe_membre("G", "a")
    cible = equiv(appartient(vy, E.classe(vG, va)), appartient(E.couple(va, vy), vG))
    assert t.conclusion == cible and t.est_clos


def test_membre_quotient():
    vG, vE, vC = var("G"), var("E"), var("C")
    t = Q.membre_quotient("G", "E", "C")
    droit = et(appartient(vC, E.parties(vE)),
               existe("x", et(appartient(var("x"), vE),
                              egal(vC, E.classe(vG, var("x"))))))
    cible = equiv(appartient(vC, E.quotient(vG, vE)), droit)
    assert t.conclusion == cible and t.est_clos


def test_classe_dans_quotient():
    vG, vE, va = var("G"), var("E"), var("a")
    t = Q.classe_dans_quotient("G", "E", "a")
    assert t.conclusion == appartient(E.classe(vG, va), E.quotient(vG, vE))
    # Hypothèses : a∈E  et  Cl_R(a)∈P(E)
    assert t.hypotheses == frozenset({
        appartient(va, vE),
        appartient(E.classe(vG, va), E.parties(vE))})
