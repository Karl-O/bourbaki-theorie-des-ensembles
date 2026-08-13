"""Tests §III — PONT liant-valeur j ↔ y (alpha_tau, débloque la chaîne du Lemme 1)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.isomorphismes_ordre import ensembles_valeur_bridge as B


def test_valeur_j_egal_y_clos():
    """⊢ valeur(f,x,b="j") = valeur(f,x,b="y")  — CLOS (alpha_tau)."""
    t = B.valeur_j_egal_y("f", "x")
    assert t.est_clos
    assert t.conclusion == B.valeur_j_egal_y_cible("f", "x")
    # non trivial : les deux côtés sont des τ DISTINCTS (lieurs j vs y)
    g, d = t.conclusion.termes[0], t.conclusion.termes[1]
    assert g != d


def test_valeur_y_egal_j_clos():
    t = B.valeur_y_egal_j("f", "x")
    assert t.est_clos
    assert t.conclusion == egal(E.valeur(var("f"), var("x"), b="y"),
                                E.valeur(var("f"), var("x"), b="j"))


def test_parametrable_autre_argument():
    """Fonctionne pour un argument ≠ x (ex. u), tant que ≠ y/j."""
    t = B.valeur_j_egal_y("g", "u")
    assert t.est_clos
    assert t.conclusion == B.valeur_j_egal_y_cible("g", "u")


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22
