"""Tests — §III.3.2 : l'ORDRE ≤ DES CARDINAUX EST TOTAL (Théorème 1).

On certifie les quatre composantes (réflexivité, transitivité, comparabilité,
antisymétrie gardée par « cardinaux ») et leur assemblage `cardinaux_ordre_total`.
Chaque test vérifie la conclusion EXACTE (clôture universelle de la relation
R{x,y} := inf_egal_card(x,y)) et la clôture (.est_clos).

NB : comparabilité (Zorn) et Cantor–Bernstein (point fixe) sont coûteux ; ces
tests sont volontairement peu nombreux et ciblés.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, ou, impl, pourtout
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux import ensembles_cardinaux_props_restantes_ordre as O
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, est_cardinal, cardinal


def test_inf_egal_reflexif_general():
    """⊢ (∀X) X ≤ X   (RÉFLEXIVITÉ de ≤)."""
    t = O.inf_egal_reflexif_general("X")
    assert t.conclusion == pourtout("X", inf_egal_card(var("X"), var("X")))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_inf_egal_transitive_general():
    """⊢ (∀X∀Y∀Z)((X≤Y et Y≤Z)⇒X≤Z)   (TRANSITIVITÉ de ≤)."""
    t = O.inf_egal_transitive_general("X", "Y", "Z")
    X, Y, Z = var("X"), var("Y"), var("Z")
    exp = pourtout("X", pourtout("Y", pourtout("Z",
        impl(et(inf_egal_card(X, Y), inf_egal_card(Y, Z)), inf_egal_card(X, Z)))))
    assert t.conclusion == exp
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_est_son_cardinal():
    """⊢ est_cardinal(a) ⇒ (Card a = a)   (un cardinal est son propre cardinal)."""
    t = O._cardinal_est_son_cardinal("a")
    assert t.conclusion == impl(est_cardinal(var("a")), egal(cardinal(var("a")), var("a")))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_inf_egal_antisymetrique_card():
    """⊢ (∀a∀b)((a≤b et b≤a et a,b cardinaux)⇒a=b)   (ANTISYMÉTRIE via Cantor–Bernstein)."""
    t = O.inf_egal_antisymetrique_card("a", "b")
    a, b = var("a"), var("b")
    exp = pourtout("a", pourtout("b",
        impl(et(et(et(inf_egal_card(a, b), inf_egal_card(b, a)),
                   est_cardinal(a)), est_cardinal(b)), egal(a, b))))
    assert t.conclusion == exp
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_inf_egal_total_general():
    """⊢ (∀X∀Y)(X≤Y ou Y≤X)   (COMPARABILITÉ : l'ordre est TOTAL ; via Zorn)."""
    t = O.inf_egal_total_general("X", "Y")
    X, Y = var("X"), var("Y")
    exp = pourtout("X", pourtout("Y", ou(inf_egal_card(X, Y), inf_egal_card(Y, X))))
    assert t.conclusion == exp
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinaux_ordre_total():
    """⊢ réflexif et transitif et antisymétrique(cardinaux) et total — ORDRE TOTAL."""
    t = O.cardinaux_ordre_total()
    assert t.est_clos
    assert t.hypotheses == frozenset()
