# -*- coding: utf-8 -*-
"""Tests — extensionnalité graphe_terme = G (B2 du chantier CST).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_graphe_terme_egalite import (
    egalite_graphe_terme, hyp_valeurs,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_est_graphe,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_graphe_terme_est_graphe_clos():
    """B1 : est_un_graphe(graphe_terme(A,T)) — CLOS."""
    th = graphe_terme_est_graphe(var("A"), E.image(var("g"), var("xg")), "xg")
    assert th.est_clos
    assert th.conclusion == E.est_un_graphe(
        E.graphe_terme(var("A"), E.image(var("g"), var("xg")), "xg"))


def test_egalite_graphe_terme():
    """🎯 B2 : {graphe, fonctionnel, dom=A, valeurs=T} ⊢ graphe_terme(A,T)=G."""
    t = E.image(var("g"), var("xg"))
    th = egalite_graphe_terme(var("A"), t, var("G"))
    assert th.conclusion == egal(E.graphe_terme(var("A"), t, "xg"), var("G"))
    assert len(th.hypotheses) == 4
    assert hyp_valeurs(var("G"), var("A"), t) in th.hypotheses
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_fonctorialite_parties_termes():
    """🎯🎯 B3 (CST1 cas 𝔓, ÉGALITÉ DE TERMES) : {borne-image ∀-close} ⊢
    ext_parties_reelle(g∘f,A) = composee(ext_g, ext_f)."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_graphe_terme_egalite import (
        fonctorialite_parties_termes,
    )
    from bourbaki.iv_structures.iv_1_structures_isomorphismes.ensembles_extension_echelon_reelle import (
        ext_parties_reelle,
    )
    th = fonctorialite_parties_termes()
    gf = E.composee(var("g"), var("f"))
    assert th.conclusion == egal(
        ext_parties_reelle(gf, "A"),
        E.composee(ext_parties_reelle("g", "B"), ext_parties_reelle("f", "A")))
    assert len(th.hypotheses) == 1
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_composee_support():
    """B3-support : composee_est_graphe CLOS + dom_composee_borne 2 hyps."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_composee_graphe_support import (
        composee_est_graphe, dom_composee_borne,
    )
    assert composee_est_graphe().est_clos
    assert len(dom_composee_borne().hypotheses) == 2
