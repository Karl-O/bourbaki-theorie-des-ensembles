"""Tests — §III.6.3 Théorème 2 (HESSENBERG), pièces du MAXIMAL au CARRÉ.

maximal_carre_egal (𝔟²=𝔟) / hessenberg_a_carre_inf_egal (≥ dur) /
hessenberg_aa_egal_de_maximal (a²=a sous 2 hyps honnêtes).  theorie=22, non vacuous."""
from __future__ import annotations

from bourbaki.logique.formule import egal, var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, est_bijection_de
from bourbaki.cardinaux.ensembles_hessenberg import (
    enonce_hard_aa_inf_egal_a, enonce_hessenberg,
)
from bourbaki.cardinaux.ensembles_hessenberg_maximal_card import (
    maximal_carre_egal, hessenberg_a_carre_inf_egal, hessenberg_aa_egal_de_maximal,
)


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22


def test_maximal_carre_egal():
    r = maximal_carre_egal("S0", "phi0")
    vS = var("S0")
    SxS = E.produit(vS, vS)
    # 𝔟² = 𝔟 au niveau ensembliste : Card(S×S) = Card(S)
    assert r.conclusion == egal(cardinal(SxS), cardinal(vS))
    # hyp honnête unique : la bijectivité de φ
    assert est_bijection_de(var("phi0"), SxS, vS) in r.hypotheses
    assert r.conclusion not in r.hypotheses
    assert len(theorie_ensembles().axiomes) == 22


def test_hessenberg_a_carre_inf_egal():
    r = hessenberg_a_carre_inf_egal("E", "S0")
    # conclusion LITTÉRALEMENT enonce_hard (le ≥ dur)
    assert r.conclusion == enonce_hard_aa_inf_egal_a("E")
    cE, cS = cardinal(var("E")), cardinal(var("S0"))
    SxS = E.produit(var("S0"), var("S0"))
    assert egal(cS, cE) in r.hypotheses
    assert egal(cardinal(SxS), cS) in r.hypotheses
    assert r.conclusion not in r.hypotheses
    assert len(theorie_ensembles().axiomes) == 22


def test_hessenberg_aa_egal_de_maximal():
    r = hessenberg_aa_egal_de_maximal("E", "S0")
    # a²=a (Théorème 2) sous est_infini : conclusion = enonce_hessenberg(E)
    assert r.conclusion == enonce_hessenberg("E")
    cE, cS = cardinal(var("E")), cardinal(var("S0"))
    SxS = E.produit(var("S0"), var("S0"))
    assert egal(cS, cE) in r.hypotheses
    assert egal(cardinal(SxS), cS) in r.hypotheses
    assert r.conclusion not in r.hypotheses
    assert len(theorie_ensembles().axiomes) == 22
