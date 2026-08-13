# -*- coding: utf-8 -*-
"""Tests — LE RECOLLEMENT INDEXÉ (P5-P7 de S3, §II.4.8, la 🎯).

Un test par palier : P6 injectivité [CLOS], P4/P5 image [4 hyps], P7 bijection,
Eq(E, ⊔ fibres) 🎯, Card(E) = somme_cardinale(Xfib, F).
theorie_ensembles()==22 avant/après."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, appartient)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de, equipotent, cardinal, somme_cardinale)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_fibres_famille import (
    famille_fibres, somme_fibres, hypothese_fonctionnelle, hypothese_domaine,
    hypothese_valeurs, hypothese_pont_fam)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_decomposition_fibres import (
    graphe_marquage)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_decomposition_fibres_bij import (
    decomposition_injective, decomposition_image, decomposition_bijection,
    eq_decomposition_fibres, card_decomposition_fibres)

_HYPS = frozenset({hypothese_fonctionnelle(), hypothese_domaine(),
                   hypothese_valeurs(), hypothese_pont_fam()})


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_p6_decomposition_injective():
    """P6 ⊢ injective_dans(Φ, E) — CLOS (pas d'extensionnalité)."""
    thm = decomposition_injective()
    assert thm.est_clos
    assert thm.conclusion == E.injective_dans(graphe_marquage(), var("Efb"))


def test_p4_p5_decomposition_image():
    """P4/P5 {Hf1, Hf2, Hf3, HF} ⊢ image(Φ, E) = ⊔_{y∈F} f⁻¹⟨{y}⟩."""
    thm = decomposition_image()
    assert thm.conclusion == egal(E.image(graphe_marquage(), var("Efb")),
                                  somme_fibres())
    assert thm.hypotheses == _HYPS


def test_p7_decomposition_bijection():
    """P7 {Hf1, Hf2, Hf3, HF} ⊢ est_bijection_de(Φ, E, ⊔)."""
    thm = decomposition_bijection()
    assert thm.conclusion == est_bijection_de(graphe_marquage(), var("Efb"),
                                              somme_fibres())
    assert thm.hypotheses == _HYPS


def test_p7_eq_decomposition_fibres():
    """🎯 {Hf1, Hf2, Hf3, HF} ⊢ Eq( E , somme_famille(Xfib, F) )."""
    thm = eq_decomposition_fibres()
    assert thm.conclusion == equipotent(var("Efb"),
                                        E.somme_famille(famille_fibres(), var("Ffb")))
    assert thm.hypotheses == _HYPS


def test_p7_card_decomposition_fibres():
    """{Hf1, Hf2, Hf3, HF} ⊢ Card(E) = Card(⊔) — le RHS EST somme_cardinale(Xfib, F)."""
    thm = card_decomposition_fibres()
    assert thm.conclusion == egal(cardinal(var("Efb")), cardinal(somme_fibres()))
    assert cardinal(somme_fibres()) == somme_cardinale(famille_fibres(), var("Ffb"))
    assert thm.hypotheses == _HYPS
    assert len(E.theorie_ensembles().axiomes) == 22
