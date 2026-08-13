# -*- coding: utf-8 -*-
"""Tests — ADJONCTION D'INDICE au produit d'une famille (T1b-(2), §II.5.5 Rem.1).

Un test par palier : P1 fonctionnel, P2 valeur, P3 domaine, briques (restriction,
graphe, valeurs de réunion, prolongement), P6 injectivité, P4/P5 image, P7
bijection + Eq + Card.  theorie_ensembles() == 22 avant/après."""
import pytest
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, appartient
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de, equipotent, cardinal)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction import (
    indices_adjoints, produit_total, produit_cible, graphe_adjonction,
    hypothese_indice_neuf, hypothese_graphes_total, hypothese_graphes_partiel,
    j_dans_union, inclusion_I_union, adjonction_fonctionnelle, adjonction_domaine,
    adjonction_valeur)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_briques import (
    restriction_dans_produit, restriction_est_graphe, valeur_reunion_gauche,
    valeur_reunion_point, prolongement_un_point_dans_produit)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_bij import (
    adjonction_injective, adjonction_image, adjonction_bijection,
    eq_produit_adjonction, produit_cardinal_adjonction)

pytestmark = pytest.mark.slow


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ── P1 / P2 / P3 : Φ fonction sur tout le produit total ───────────────────────
def test_p1_adjonction_fonctionnelle():
    """P1 ⊢ est_fonctionnel(Φ) — CLOS."""
    thm = adjonction_fonctionnelle()
    assert thm.est_clos
    assert thm.conclusion == E.est_fonctionnel(graphe_adjonction())


def test_p2_adjonction_valeur():
    """P2 {G∈∏_{I∪{j}}} ⊢ Φ(G) = (G|I, G(j)[τc]) — 1 hyp honnête."""
    thm = adjonction_valeur()
    assert thm.hypotheses == frozenset({appartient(var("Gq"), produit_total())})


def test_p3_adjonction_domaine():
    """P3 ⊢ dom Φ = ∏_{I∪{j}} — CLOS."""
    thm = adjonction_domaine()
    assert thm.est_clos
    assert thm.conclusion == egal(E.dom(graphe_adjonction()), produit_total())


# ── Briques d'infrastructure ──────────────────────────────────────────────────
def test_membership_union_indices():
    """⊢ j∈I∪{j} (clos) et ⊢ I ⊂ I∪{j} (clos)."""
    assert j_dans_union().est_clos
    assert inclusion_I_union().est_clos


def test_restriction_dans_produit():
    """{t∈∏_{I∪{j}}} ⊢ t|I ∈ ∏_I — 1 hyp honnête."""
    thm = restriction_dans_produit(var("tq"))
    assert thm.hypotheses == frozenset({appartient(var("tq"), produit_total())})
    assert thm.conclusion == appartient(E.restriction(var("tq"), var("Iq")),
                                        E.produit_famille(var("uq"), var("Iq")))


def test_restriction_est_graphe():
    """⊢ est_un_graphe(f|X) — CLOS (dérivé de AXIOME_RESTRICTION)."""
    assert restriction_est_graphe(var("Gq"), var("Iq")).est_clos


def test_valeurs_reunion():
    """(G∪H)(t)=G(t) [2 hyps] et (G∪{(j,x)})(j)=x [1 hyp]."""
    assert len(valeur_reunion_gauche(var("Gq"), var("Hq"), var("tq")).hypotheses) == 2
    assert len(valeur_reunion_point(var("Gq"), var("jq"), var("xq")).hypotheses) == 1


def test_prolongement_un_point():
    """{G∈∏_I, x∈u_j, ¬(j∈I)} ⊢ G∪{(j,x)} ∈ ∏_{I∪{j}} — 3 hyps honnêtes."""
    thm = prolongement_un_point_dans_produit(var("Gq"), var("xq"))
    assert len(thm.hypotheses) == 3
    assert hypothese_indice_neuf() in thm.hypotheses


# ── P6 : injectivité ──────────────────────────────────────────────────────────
def test_p6_adjonction_injective():
    """{H2} ⊢ injective_dans(Φ, ∏_{I∪{j}})."""
    thm = adjonction_injective()
    assert thm.conclusion == E.injective_dans(graphe_adjonction(), produit_total())
    assert thm.hypotheses == frozenset({hypothese_graphes_total()})


# ── P4/P5 : image (⊂ et surjectivité) ─────────────────────────────────────────
def test_p4_p5_adjonction_image():
    """{H1, H3} ⊢ image(Φ, ∏_{I∪{j}}) = (∏_I) × u_j."""
    thm = adjonction_image()
    assert thm.conclusion == egal(E.image(graphe_adjonction(), produit_total()),
                                  produit_cible())
    assert thm.hypotheses == frozenset({hypothese_indice_neuf(),
                                        hypothese_graphes_partiel()})


# ── P7 : bijection, équipotence, cardinal ─────────────────────────────────────
def test_p7_adjonction_bijection():
    """{H1, H2, H3} ⊢ est_bijection_de(Φ, ∏_{I∪{j}}, ∏_I × u_j)."""
    thm = adjonction_bijection()
    assert thm.conclusion == est_bijection_de(graphe_adjonction(),
                                              produit_total(), produit_cible())
    assert thm.hypotheses == frozenset({hypothese_indice_neuf(),
                                        hypothese_graphes_total(),
                                        hypothese_graphes_partiel()})


def test_p7_eq_produit_adjonction():
    """{H1, H2, H3} ⊢ Eq(∏_{I∪{j}}, ∏_I × u_j)."""
    thm = eq_produit_adjonction()
    assert thm.conclusion == equipotent(produit_total(), produit_cible())
    assert len(thm.hypotheses) == 3


def test_p7_produit_cardinal_adjonction():
    """{H1, H2, H3} ⊢ Card(∏_{I∪{j}}) = Card(∏_I × u_j) = pcb(∏_I, u_j)."""
    thm = produit_cardinal_adjonction()
    assert thm.conclusion == egal(cardinal(produit_total()), cardinal(produit_cible()))
    # forme cardinale exacte : le RHS EST le terme produit_cardinal_binaire(∏_I, u_j)
    assert cardinal(produit_cible()) == produit_cardinal_binaire(
        E.produit_famille(var("uq"), var("Iq")), E.valeur_famille(var("uq"), var("jq")))
    assert len(thm.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22
