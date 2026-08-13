# -*- coding: utf-8 -*-
"""Tests — CST2 briques d'étage : bijectivité de l'extension aux parties."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
from bourbaki.iv_structures.iv_2_morphismes_structures_derivees.cst_criteres.ensembles_cst2_briques import (
    bijection_q, ext_parties_bijective_q,
)


def test_ext_parties_bijective_q():
    """🎯 {func g, dom g=A, func g⁻¹, g⟨A⟩=A'} ⊢ Q(ext_P(g), 𝔓A, 𝔓A') — 4 hyps."""
    th = ext_parties_bijective_q("g", "A", "Ap")
    assert len(th.hypotheses) == 4
    attendu = {E.est_fonctionnel(var("g")),
               E.est_fonctionnel(E.reciproque(var("g")))}
    assert attendu <= set(th.hypotheses)


def test_ext_parties_sur_termes():
    """Aux TERMES composés (A := 𝔓E, A' := 𝔓E') — l'étage se recurse."""
    A, Ap = E.parties(var("Eb1")), E.parties(var("Ep1"))
    th = ext_parties_bijective_q(var("g"), A, Ap, "xg2")
    assert len(th.hypotheses) == 4
    assert th.conclusion == bijection_q(
        E.graphe_terme(E.parties(A), E.image(var("g"), var("xg2")), "xg2"),
        E.parties(A), E.parties(Ap))
    assert len(E.theorie_ensembles().axiomes) == 22
