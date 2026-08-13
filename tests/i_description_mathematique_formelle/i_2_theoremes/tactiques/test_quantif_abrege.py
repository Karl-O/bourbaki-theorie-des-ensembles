"""Tests V9 — couche quantifiée abrégée (monotonie/congruence ∀/∃, élim ∃)."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient, impl, equiv, existe, pourtout, egal, tau, subst_f
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro, projection_droite
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (monotonie_pour_tout, monotonie_existe,
                                      existe_vacuous, existe_elimination,
                                      congruence_pour_tout, congruence_existe,
                                      alpha_pour_tout, alpha_existe)

vx, a, b = var("x"), var("a"), var("b")
R = appartient(vx, a)


def test_existe_temoin_primitive():
    # ⊢ (∃x)R ⇒ (τx(R)|x)R, primitive saine (identité-τ)
    t = N.existe_temoin(R, "x")
    assert t.conclusion == impl(existe("x", R), subst_f(tau("x", R), "x", R))
    assert t.est_clos


def test_monotonie_pour_tout():
    t = monotonie_pour_tout(a_implique_a(R), "x")
    assert t.conclusion == impl(pourtout("x", R), pourtout("x", R)) and t.est_clos


def test_monotonie_existe():
    t = monotonie_existe(a_implique_a(R), "x")
    assert t.conclusion == impl(existe("x", R), existe("x", R)) and t.est_clos


def test_existe_vacuous():
    c = egal(a, b)                       # pas de x libre
    t = existe_vacuous(c, "x")
    assert t.conclusion == impl(existe("x", c), c) and t.est_clos


def test_existe_elimination():
    c = egal(a, b)
    # implication CLOSE (x∈a et a=b) ⇒ (a=b) ; x non libre dans C ni dans Γ(=∅)
    thm = projection_droite(R, c)        # ⊢ (R et C) ⇒ C
    t = existe_elimination(thm, "x")
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et
    assert t.conclusion == impl(existe("x", et(R, c)), c) and t.est_clos


def test_congruence_existe():
    eq = conjonction_intro(a_implique_a(R), a_implique_a(R))   # R⇔R
    t = congruence_existe(eq, "x")
    assert t.conclusion == equiv(existe("x", R), existe("x", R)) and t.est_clos


def test_congruence_pour_tout():
    eq = conjonction_intro(a_implique_a(R), a_implique_a(R))
    t = congruence_pour_tout(eq, "x")
    assert t.conclusion == equiv(pourtout("x", R), pourtout("x", R)) and t.est_clos


def test_alpha_pour_tout():
    # ⊢ (∀x)(x∈a) ⇔ (∀u)(u∈a)
    t = alpha_pour_tout("x", "u", R)
    assert t.conclusion == equiv(pourtout("x", R), pourtout("u", appartient(var("u"), a)))
    assert t.est_clos


def test_alpha_existe():
    t = alpha_existe("x", "u", R)
    assert t.conclusion == equiv(existe("x", R), existe("u", appartient(var("u"), a)))
    assert t.est_clos


def test_et_existe_droite():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import et_existe_droite
    P = appartient(a, b)                       # pas de y libre
    Q = appartient(var("y"), a)                # contient y
    t = et_existe_droite(P, "y", Q)
    assert t.conclusion == equiv(et(P, existe("y", Q)), existe("y", et(P, Q))) and t.est_clos


def test_existe_commute():
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import existe_commute
    t = existe_commute("x", "y", R)
    assert t.conclusion == equiv(existe("x", existe("y", R)), existe("y", existe("x", R)))
    assert t.est_clos


def test_assoc_et():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import et
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import assoc_et
    P, Q, S = appartient(a, b), appartient(b, a), appartient(a, a)
    t = assoc_et(P, Q, S)
    assert t.conclusion == equiv(et(P, et(Q, S)), et(et(P, Q), S)) and t.est_clos
