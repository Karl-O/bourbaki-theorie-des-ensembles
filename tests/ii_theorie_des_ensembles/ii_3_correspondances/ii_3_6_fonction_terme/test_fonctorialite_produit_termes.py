# -*- coding: utf-8 -*-
"""Tests — F2-TERMES (CST1 cas ×, égalité de termes) + pr_dans.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, appartient
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonctorialite_produit_termes import (
    pr_dans, fonctorialite_produit_termes,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_pr_dans():
    """{u∈A×B} ⊢ pr₁u∈A ∧ pr₂u∈B — le lemme de projections."""
    th = pr_dans(var("u"), var("A"), var("B"))
    assert th.conclusion == et(appartient(E.pr1(var("u")), var("A")),
                               appartient(E.pr2(var("u")), var("B")))
    assert len(th.hypotheses) == 1


def test_fonctorialite_produit_termes():
    """🎯🎯 F2-TERMES (CST1 cas ×) : {est_application ×4} ⊢
    produit_app(g∘f, g'∘f') = composee(prod_g, prod_f)."""
    from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
        produit_app_reelle,
    )
    th = fonctorialite_produit_termes()
    gf = E.composee(var("g"), var("f"))
    gpfp = E.composee(var("gp"), var("fp"))
    assert th.conclusion == egal(
        produit_app_reelle(gf, gpfp, "A", "B"),
        E.composee(produit_app_reelle("g", "gp", "Ap", "Bp"),
                   produit_app_reelle("f", "fp", "A", "B")))
    assert len(th.hypotheses) == 4
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
