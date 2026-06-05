"""Tests V9 — couche abrégée (formules à ∀/∃/Coll primitifs, chemin Bourbaki).

Vérifie : substitution capture-évitante, constructibilité de A1/A2 SANS gonflement,
affichage, et le pont `developper` (abrégé → assemblage-τ) sur un petit cas.

python -m pytest V9/test_formule.py -v
"""
from __future__ import annotations

import formule as F
from formule import (var, egal, appartient, inclus, non, ou, et, impl,
                     pourtout, existe, coll, subst_f, libres_f, afficher_f)
from lecture import est_relation


# ── Axiomes du chapitre II, construits SANS explosion ─────────────────────────
A1 = pourtout("x", pourtout("y",
        impl(et(inclus(var("x"), var("y")), inclus(var("y"), var("x"))),
             egal(var("x"), var("y")))))

A2 = pourtout("x", pourtout("y",
        coll("z", ou(egal(var("z"), var("x")), egal(var("z"), var("y"))))))


def test_a1_a2_petits_et_clos():
    # Constructibles instantanément (pas de MemoryError) et fermés (0 var libre).
    assert isinstance(A1, F.Formule) and libres_f(A1) == set()
    assert isinstance(A2, F.Formule) and libres_f(A2) == set()


def test_libres():
    f = pourtout("x", appartient(var("x"), var("y")))   # (∀x)(x∈y)
    assert libres_f(f) == {"y"}                          # x liée, y libre


def test_substitution_simple():
    f = appartient(var("x"), var("y"))                   # x∈y
    g = subst_f(var("a"), "x", f)                        # (a|x)
    assert g == appartient(var("a"), var("y"))


def test_substitution_capture_evitante():
    # (y|x) dans (∃y)(x∈y) ne doit PAS capturer : y est renommé.
    f = existe("y", appartient(var("x"), var("y")))
    g = subst_f(var("y"), "x", f)
    assert g.tag == "exists" and g.lieur != "y"          # quantificateur renommé
    assert "y" in libres_f(g)                            # le y substitué reste libre


def test_substitution_sous_lieur_inerte():
    # (a|x) dans (∀x)(x∈z) ne change rien (x est liée).
    f = pourtout("x", appartient(var("x"), var("z")))
    assert subst_f(var("a"), "x", f) == f


def test_affichage():
    assert afficher_f(egal(var("x"), var("y"))) == "(x = y)"
    # A2 = (∀x)(∀y) Coll_z(...) ; Coll s'affiche par sa définition (∃…)(∀…)
    assert afficher_f(A2).startswith("(∀x) (∀y) (∃")
    # ⇒ et ∀ sont reconnus dans A1
    from formule import impl, var as v
    assert afficher_f(impl(egal(v("a"), v("b")), egal(v("c"), v("d")))) == "((a = b) ⇒ (c = d))"
    assert afficher_f(A1).startswith("(∀x) (∀y)")


def test_alpha_equivalence():
    from formule import alpha_egal, existe, appartient, var as v
    # (∃x)(x∈u) ≡ (∃w)(w∈u) à renommage près, mais ≠ structurellement
    f = existe("x", appartient(v("x"), v("u")))
    g = existe("w", appartient(v("w"), v("u")))
    assert alpha_egal(f, g) and f != g
    # variable libre non renommée : (∃x)(x∈u) ≢ (∃x)(x∈t)
    assert not alpha_egal(f, existe("x", appartient(v("x"), v("t"))))


def test_pont_developper_petit_cas():
    # (∀x)(x = x) : petit, développable en assemblage-τ, qui est une relation.
    f = pourtout("x", egal(var("x"), var("x")))
    asm = F.developper_f(f)
    assert est_relation(asm)
    # cohérence : développer (a|x)(x=x) = (a=a)
    inst = F.developper_f(egal(var("a"), var("a")))
    from assemblage import egalite, Assemblage
    assert inst == egalite(Assemblage(("a",)), Assemblage(("a",)))
