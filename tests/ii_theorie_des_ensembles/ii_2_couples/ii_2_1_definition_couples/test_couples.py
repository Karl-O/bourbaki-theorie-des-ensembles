"""Tests V9 — §II.2 Couples : définition, projections, égalité de coordonnées,
et la couche égalitaire abrégée (symétrie, transitivité, congruence C44)."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, equiv, app, tau, existe, afficher_f
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import couple, pr1, pr2, paire, singleton
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import couple_egal_si_composantes
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (singleton_membre, singleton_injectif,
                               singleton_egale_paire, membre_paire_gauche,
                               membre_paire_droite, paire_cancellation,
                               couple_egal_implique_composantes, proposition_1)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (symetrie, transitivite, composer_egalites,
                                      congruence_terme)


# ── Définition du couple et des projections (fidélité Bourbaki) ────────────────
def test_couple_terme():
    x, y = var("x"), var("y")
    assert couple(x, y) == paire(singleton(x), paire(x, y))


def test_projections():
    z = var("z")
    x, y = var("x"), var("y")
    assert pr1(z) == tau("x", existe("y", egal(z, couple(x, y))))
    assert pr2(z) == tau("y", existe("x", egal(z, couple(x, y))))


# ── Couche égalitaire abrégée ──────────────────────────────────────────────────
def test_symetrie():
    a, b = var("a"), var("b")
    t = symetrie(a, b)
    assert t.conclusion == impl(egal(a, b), egal(b, a)) and t.est_clos


def test_transitivite():
    a, b, c = var("a"), var("b"), var("c")
    t = transitivite(a, b, c)
    assert t.conclusion == egal(a, c)
    assert t.hypotheses == {egal(a, b), egal(b, c)}


def test_composer_egalites():
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
    a, b, c = var("a"), var("b"), var("c")
    hab = N.assume(egal(a, b))
    hbc = N.assume(egal(b, c))
    tac = composer_egalites(hab, hbc)
    assert tac.conclusion == egal(a, c)
    assert tac.hypotheses == {egal(a, b), egal(b, c)}


def test_congruence_terme():
    a, b, d = var("a"), var("b"), var("d")
    V = app("f", var("w"), d)                 # V{w} = f(w, d)
    t = congruence_terme(a, b, V)
    assert t.conclusion == impl(egal(a, b), egal(app("f", a, d), app("f", b, d)))
    assert t.est_clos


# ── Lemmes d'injectivité des paires ────────────────────────────────────────────
def test_singleton_membre():
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import appartient
    a, c = var("a"), var("c")
    t = singleton_membre(a, c)                  # (a∈{c}) ⇔ (a=c)
    assert t.conclusion == equiv(appartient(a, singleton(c)), egal(a, c))
    assert t.est_clos


def test_singleton_injectif():
    x, xp = var("x"), var("xp")
    t = singleton_injectif("x", "xp")
    assert t.conclusion == impl(egal(singleton(x), singleton(xp)), egal(x, xp)) and t.est_clos


def test_singleton_egale_paire():
    c, a, b = var("c"), var("a"), var("b")
    t = singleton_egale_paire("c", "a", "b")
    cible = impl(egal(singleton(c), paire(a, b)), et(egal(a, c), egal(b, c)))
    assert t.conclusion == cible and t.est_clos


def test_membre_paire():
    a, b = var("a"), var("b")
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import appartient
    assert membre_paire_gauche(a, b).conclusion == appartient(a, paire(a, b))
    assert membre_paire_droite(a, b).conclusion == appartient(b, paire(a, b))
    assert membre_paire_gauche(a, b).est_clos


def test_paire_cancellation():
    a, b, c = var("a"), var("b"), var("c")
    t = paire_cancellation(a, b, c)
    assert t.conclusion == impl(egal(paire(a, b), paire(a, c)), egal(b, c)) and t.est_clos


# ── Proposition 1 ──────────────────────────────────────────────────────────────
def test_couple_egal_si_composantes():
    vx, vy, vxp, vyp = var("x"), var("y"), var("xp"), var("yp")
    t = couple_egal_si_composantes("x", "y", "xp", "yp")
    cible = impl(et(egal(vx, vxp), egal(vy, vyp)),
                 egal(couple(vx, vy), couple(vxp, vyp)))
    assert t.conclusion == cible and t.est_clos


def test_couple_egal_implique_composantes():
    vx, vy, vxp, vyp = var("x"), var("y"), var("xp"), var("yp")
    t = couple_egal_implique_composantes("x", "y", "xp", "yp")
    cible = impl(egal(couple(vx, vy), couple(vxp, vyp)),
                 et(egal(vx, vxp), egal(vy, vyp)))
    assert t.conclusion == cible and t.est_clos


def test_proposition_1():
    vx, vy, vxp, vyp = var("x"), var("y"), var("xp"), var("yp")
    t = proposition_1("x", "y", "xp", "yp")
    P = egal(couple(vx, vy), couple(vxp, vyp))
    Q = et(egal(vx, vxp), egal(vy, vyp))
    assert t.conclusion == equiv(P, Q) and t.est_clos
