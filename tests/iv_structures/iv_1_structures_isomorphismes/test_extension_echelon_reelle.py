# -*- coding: utf-8 -*-
"""Tests — extensions canoniques RÉELLES (T1 du chantier CST).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
    ext_parties_reelle, ext_parties_fonctionnel, ext_parties_valeur,
    produit_app_reelle, produit_app_fonctionnel, produit_app_valeur,
    terme_ext_parties, terme_produit_app,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_ext_parties_fonctionnel_clos():
    """est_fonctionnel(ḡ) — CLOS 0 hyp (le mur opaque de juillet est contourné)."""
    th = ext_parties_fonctionnel("g", "A")
    assert th.est_clos
    assert th.conclusion == E.est_fonctionnel(ext_parties_reelle("g", "A"))


def test_ext_parties_valeur():
    """{X∈𝔓A} ⊢ ḡ(X) = g⟨X⟩ — la caractérisation de valeur réelle."""
    th = ext_parties_valeur("g", "A")
    assert len(th.hypotheses) == 1
    assert th.conclusion == egal(
        E.valeur(ext_parties_reelle("g", "A"), var("pcs")),
        E.image(var("g"), var("pcs")))


def test_produit_app_fonctionnel_clos():
    th = produit_app_fonctionnel("g", "h", "A", "B")
    assert th.est_clos
    assert th.conclusion == E.est_fonctionnel(produit_app_reelle("g", "h", "A", "B"))


def test_produit_app_valeur():
    """{u∈A×B} ⊢ (g×h)(u) = (g(pr₁u), h(pr₂u)) — l'écart n°86 contourné en réel."""
    th = produit_app_valeur("g", "h", "A", "B")
    assert len(th.hypotheses) == 1
    assert th.conclusion == egal(
        E.valeur(produit_app_reelle("g", "h", "A", "B"), var("pcs")),
        E.couple(E.valeur(var("g"), E.pr1(var("pcs"))),
                 E.valeur(var("h"), E.pr2(var("pcs")))))
    assert len(E.theorie_ensembles().axiomes) == 22


def test_valeur_en_point_arbitraire():
    """🎯 Le point est ARBITRAIRE (lecture VARIABLE, pas constante) : au point Y,
    ḡ(Y) = g⟨Y⟩ — le test discriminant de la convention xg (axiome C54 unique)."""
    th = ext_parties_valeur("g", "A", var("Y"))
    assert th.conclusion == egal(
        E.valeur(ext_parties_reelle("g", "A"), var("Y")),
        E.image(var("g"), var("Y")))
    th2 = produit_app_valeur("g", "h", "A", "B", var("Y"))
    assert th2.conclusion == egal(
        E.valeur(produit_app_reelle("g", "h", "A", "B"), var("Y")),
        E.couple(E.valeur(var("g"), E.pr1(var("Y"))),
                 E.valeur(var("h"), E.pr2(var("Y")))))


def test_fonctorialite_parties_valeur():
    """🎯 F1-val (CST1 cas 𝔓) : {X∈𝔓A, f⟨X⟩∈𝔓B} ⊢ ⟨g∘f⟩(X) = ⟨g⟩(⟨f⟩(X))."""
    from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
        fonctorialite_parties_valeur,
    )
    th = fonctorialite_parties_valeur()
    gf = E.composee(var("g"), var("f"))
    lhs = E.valeur(ext_parties_reelle(gf, "A"), var("Xf1"))
    rhs = E.valeur(ext_parties_reelle("g", "B"),
                   E.valeur(ext_parties_reelle("f", "A"), var("Xf1")))
    assert th.conclusion == egal(lhs, rhs)
    assert len(th.hypotheses) == 2
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_fonctorialite_produit_valeur():
    """🎯 F2-val (CST1 cas ×) : 8 hyps structurelles ⊢ ((g×gp)∘(f×fp))(U) composé."""
    from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
        fonctorialite_produit_valeur,
    )
    th = fonctorialite_produit_valeur()
    assert len(th.hypotheses) == 8
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
