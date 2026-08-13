# -*- coding: utf-8 -*-
"""Tests — la famille des fibres (P1-P2 de S3, §II.4.8).

Un test par palier : P1a fonctionnelle [CLOS], P1b valeur [1 hyp], P1c au terme
(pont HF), P2 x∈f⁻¹⟨{f(x)}⟩ [2 hyps].  theorie_ensembles()==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_fibres_famille import (
    fibre, famille_fibres, somme_fibres, hypothese_domaine, hypothese_pont_fam,
    famille_fibres_fonctionnelle, famille_fibres_valeur, fam_fibre_egale,
    membre_fibre_de_sa_valeur)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_p1a_famille_fibres_fonctionnelle():
    """P1a ⊢ est_fonctionnel(Xfib) — CLOS."""
    thm = famille_fibres_fonctionnelle()
    assert thm.est_clos
    assert thm.conclusion == E.est_fonctionnel(famille_fibres())


def test_p1b_famille_fibres_valeur():
    """P1b {i0∈F} ⊢ Xfib(i0) = f⁻¹⟨{i0}⟩ — 1 hyp honnête."""
    thm = famille_fibres_valeur()
    assert thm.conclusion == egal(E.valeur(famille_fibres(), var("i0fb")),
                                  fibre("ffb", var("i0fb")))
    assert thm.hypotheses == frozenset({appartient(var("i0fb"), var("Ffb"))})


def test_p1c_fam_fibre_egale_au_terme():
    """P1c : Γ⊢t∈F ⟹ Γ∪{HF} ⊢ valeur_famille(Xfib,t) = f⁻¹⟨{t}⟩ (t TERME)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
    tt = E.valeur(var("ffb"), var("t0fb"))            # un TERME τ-valué (le cas dur)
    hin = N.assume(appartient(tt, var("Ffb")))
    thm = fam_fibre_egale(hin, tt)
    assert thm.conclusion == egal(E.valeur_famille(famille_fibres(), tt),
                                  fibre("ffb", tt))
    assert thm.hypotheses == frozenset({appartient(tt, var("Ffb")),
                                        hypothese_pont_fam()})


def test_p2_membre_fibre_de_sa_valeur():
    """P2 {dom f=E, x∈E} ⊢ x ∈ f⁻¹⟨{f(x)}⟩ — 2 hyps honnêtes."""
    thm = membre_fibre_de_sa_valeur()
    vx = var("xfb0")
    assert thm.conclusion == appartient(vx, fibre("ffb", E.valeur(var("ffb"), vx)))
    assert thm.hypotheses == frozenset({hypothese_domaine(),
                                        appartient(vx, var("Efb"))})
    assert len(E.theorie_ensembles().axiomes) == 22


def test_somme_fibres_forme():
    """Le terme-cible : ⊔ = somme_famille(Xfib, F) (ancrage de forme)."""
    assert somme_fibres() == E.somme_famille(famille_fibres(), var("Ffb"))
