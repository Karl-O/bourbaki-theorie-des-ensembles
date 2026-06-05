"""Tests V9 — théorèmes du chapitre II utilisant A1 (extensionnalité) et A2 (paire)."""
from __future__ import annotations

from bourbaki.logique.formule import var, egal, inclus, et, impl, ou, non, appartient, equiv, pourtout, afficher_f
from bourbaki.ensembles.ensembles_abrege import paire, singleton, VIDE, reunion, intersection
from bourbaki.ensembles.ensembles_theoremes import (extensionnalite_appliquee, existence_paire,
                                 unicite_par_extension, unicite_paire,
                                 appartient_paire_gauche, appartient_paire_droite,
                                 appartient_singleton, vide_sans_element,
                                 commutativite_paire, inclusion_reunion_gauche,
                                 commutativite_reunion, inclusion_intersection_gauche,
                                 commutativite_intersection)


def test_extensionnalite_appliquee():
    # ⊢ (a⊂b et b⊂a) ⇒ a=b   (instance de A1)
    t = extensionnalite_appliquee("a", "b")
    cible = impl(et(inclus(var("a"), var("b")), inclus(var("b"), var("a"))),
                 egal(var("a"), var("b")))
    assert t.conclusion == cible and t.est_clos


def test_existence_paire():
    # ⊢ Coll_z(z=a ou z=b)   (instance de A2 ; la paire {a,b} existe)
    t = existence_paire("a", "b")
    assert t.est_clos
    aff = afficher_f(t.conclusion)
    # contient z=a et z=b sous la structure de Coll (∃…)(∀z)((z∈…) ⇔ (z=a ∨ z=b))
    assert "(z = a)" in aff and "(z = b)" in aff and aff.startswith("(∃")


def test_unicite_par_extension():
    # {(∀z)(z∈u ⇔ R), (∀z)(z∈v ⇔ R)} ⊢ u=v
    t = unicite_par_extension("u", "v")
    assert t.conclusion == egal(var("u"), var("v"))
    R = ou(egal(var("z"), var("a")), egal(var("z"), var("b")))
    h1 = pourtout("z", equiv(appartient(var("z"), var("u")), R))
    h2 = pourtout("z", equiv(appartient(var("z"), var("v")), R))
    assert t.hypotheses == {h1, h2}


def test_unicite_paire():
    # la paire {a,b} est unique
    t = unicite_paire("a", "b", "u", "v")
    assert t.conclusion == egal(var("u"), var("v")) and len(t.hypotheses) == 2


def test_appartenance_paire():
    a, b = var("a"), var("b")
    assert appartient_paire_gauche("a", "b").conclusion == appartient(a, paire(a, b))
    assert appartient_paire_droite("a", "b").conclusion == appartient(b, paire(a, b))
    assert appartient_paire_gauche("a", "b").est_clos


def test_appartenance_singleton():
    a = var("a")
    assert appartient_singleton("a").conclusion == appartient(a, singleton(a))


def test_vide_sans_element():
    t = vide_sans_element("a")
    assert t.conclusion == non(appartient(var("a"), VIDE)) and t.est_clos


def test_commutativite_paire():
    a, b = var("a"), var("b")
    t = commutativite_paire("a", "b")
    assert t.conclusion == egal(paire(a, b), paire(b, a)) and t.est_clos


def test_inclusion_reunion_gauche():
    a, b = var("a"), var("b")
    t = inclusion_reunion_gauche("a", "b")
    assert t.conclusion == inclus(a, reunion(a, b)) and t.est_clos


def test_commutativite_reunion():
    a, b = var("a"), var("b")
    t = commutativite_reunion("a", "b")
    assert t.conclusion == egal(reunion(a, b), reunion(b, a)) and t.est_clos


def test_inclusion_intersection_gauche():
    a, b = var("a"), var("b")
    t = inclusion_intersection_gauche("a", "b")
    assert t.conclusion == inclus(intersection(a, b), a) and t.est_clos


def test_commutativite_intersection():
    a, b = var("a"), var("b")
    t = commutativite_intersection("a", "b")
    assert t.conclusion == egal(intersection(a, b), intersection(b, a)) and t.est_clos
