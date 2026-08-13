# -*- coding: utf-8 -*-
"""Tests — le marquage Φ : x ↦ (x, f(x)) (P3-P4 de S3, §II.4.8).

Un test par palier : P3a fonctionnel [CLOS], P3b domaine [CLOS], P3c valeur
[1 hyp], pont α-τ [CLOS], P4 pointwise T[t]∈⊔ [4 hyps]."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient, subst_t)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_fibres_famille import (
    somme_fibres, hypothese_domaine, hypothese_valeurs, hypothese_pont_fam)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_decomposition_fibres import (
    XB, VC, terme_marquage, graphe_marquage, valeur_y_egal_cfb,
    marquage_fonctionnel, marquage_domaine, marquage_valeur, marque_dans_somme)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_p3a_marquage_fonctionnel():
    """P3a ⊢ est_fonctionnel(Φ) — CLOS."""
    thm = marquage_fonctionnel()
    assert thm.est_clos
    assert thm.conclusion == E.est_fonctionnel(graphe_marquage())


def test_p3b_marquage_domaine():
    """P3b ⊢ dom Φ = E — CLOS."""
    thm = marquage_domaine()
    assert thm.est_clos
    assert thm.conclusion == egal(E.dom(graphe_marquage()), var("Efb"))


def test_p3c_marquage_valeur():
    """P3c {g∈E} ⊢ Φ(g) = (g, f(g)[τcfb]) — 1 hyp honnête."""
    thm = marquage_valeur()
    vg = var("gfb")
    assert thm.conclusion == egal(E.valeur(graphe_marquage(), vg),
                                  E.couple(vg, E.valeur(var("ffb"), vg, b=VC)))
    assert thm.hypotheses == frozenset({appartient(vg, var("Efb"))})


def test_pont_alpha_tau():
    """⊢ f(x) = f(x)[τcfb] — le pont α-τ des deux écritures de la valeur, CLOS."""
    thm = valeur_y_egal_cfb("ffb", var("t0fb"))
    assert thm.est_clos


def test_p4_marque_dans_somme():
    """P4 {Hf2, Hf3, HF, t∈E} ⊢ T[t] ∈ ⊔(Xfib, F) — 4 hyps honnêtes."""
    thm = marque_dans_somme()
    Tt = subst_t(var("tfb"), XB, terme_marquage())
    assert thm.conclusion == appartient(Tt, somme_fibres())
    assert thm.hypotheses == frozenset({
        hypothese_domaine(), hypothese_valeurs(), hypothese_pont_fam(),
        appartient(var("tfb"), var("Efb"))})
    assert len(E.theorie_ensembles().axiomes) == 22
