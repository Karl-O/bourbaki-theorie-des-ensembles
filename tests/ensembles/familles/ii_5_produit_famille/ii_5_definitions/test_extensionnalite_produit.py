"""Tests §II.5.3 — EXTENSIONNALITÉ DU PRODUIT ∏_{ι∈I} X_ι.

Vérifie que `extensionnalite_produit` est CLOS (0 hyp), de conclusion EXACTEMENT
l'implication (x∈∏ et y∈∏ et graphe x et graphe y et (∀ι∈I) pr_ι x=pr_ι y) ⇒ x=y,
NON vacuous (x=y n'est pas dans l'antécédent).  theorie_ensembles() reste à 22.
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, appartient, pourtout
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions import ensembles_extensionnalite_produit as X


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_extensionnalite_produit_close():
    th = X.extensionnalite_produit("f", "I", "x_pt", "y_pt")
    assert th.est_clos
    assert len(th.hypotheses) == 0


def test_extensionnalite_produit_conclusion_exacte():
    th = X.extensionnalite_produit("f", "I", "x_pt", "y_pt")
    vf, vI, vx, vy = var("f"), var("I"), var("x_pt"), var("y_pt")
    prod = E.produit_famille(vf, vI)
    proj = pourtout("i", impl(appartient(var("i"), vI),
                              egal(E.projection_indice(vx, var("i")),
                                   E.projection_indice(vy, var("i")))))
    hyp = et(et(et(et(
        appartient(vx, prod), appartient(vy, prod)),
        E.est_un_graphe(vx)), E.est_un_graphe(vy)),
        proj)
    expected = impl(hyp, egal(vx, vy))
    assert th.conclusion == expected


def test_extensionnalite_produit_non_vacuous():
    # la conclusion x=y NE figure PAS dans l'antécédent (énoncé non trivial)
    th = X.extensionnalite_produit("f", "I", "x_pt", "y_pt")
    vx, vy = var("x_pt"), var("y_pt")
    antecedent = th.conclusion.sous[0]            # impl(f,g) = ou(non f, g) ; non f = sous[0]
    assert egal(vx, vy) != antecedent
    # plus précisément, egal(x,y) n'apparaît pas comme conjoint de l'antécédent
    from bourbaki.logique.i_1_termes_relations.formule import non
    assert antecedent.sous[0] != non(egal(vx, vy))
