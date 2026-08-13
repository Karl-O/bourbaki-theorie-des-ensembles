"""Tests — §III.3.2-3.3 MONOTONIE du PRODUIT cardinal pour ≤
(ensembles_arith_cardinale_props_produit_monotone).

        ⊢ (A ≤ A₁ et B ≤ B₁) ⇒ (A × B ≤ A₁ × B₁)     (monotonie du produit)

L'injection produit H = graphe_terme(A×B, (F(pr₁k), G(pr₂k))) (= (x,y)↦(F(x),G(y)))
réutilise les paliers fonctionnel/domaine/injectif de ensembles_produit_equipotence
et un palier IMAGE version INCLUSION (image(H,A×B) ⊂ A₁×B₁ sous F⟨A⟩⊂A₁, G⟨B⟩⊂B₁).
Cas particuliers à facteur fixe (gauche/droite) via réflexivité de ≤.  theorie=22.
"""
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, impl, inclus
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_2_monotonie import (
    ensembles_arith_cardinale_props_produit_monotone as M)


def test_theorie_intangible_22():
    """La théorie des ensembles reste à 22 axiomes (rien postulé)."""
    assert len(E.theorie_ensembles().axiomes) == 22


def test_produit_graphe_image_inclus_hyps():
    """PALIER IMAGE (version injection) — image(H,A×B) ⊂ A₁×B₁ sous 4 hypothèses
    (dom F=X, dom G=Y, F⟨X⟩⊂X₁, G⟨Y⟩⊂Y₁) ; conclusion EXACTE."""
    thm = M.produit_graphe_image_inclus()
    H = M._prod_graphe("F", "G", "X", "Y", "k")
    A = E.produit(var("X"), var("Y"))
    X1Y1 = E.produit(var("X1"), var("Y1"))
    assert thm.conclusion == inclus(E.image(H, A), X1Y1)
    assert len(thm.hypotheses) == 4
    assert not thm.est_clos


def test_inf_egal_produit_invariant_clos():
    """MONOTONIE du produit — ⊢ (A ≤ A₁ et B ≤ B₁) ⇒ (A×B ≤ A₁×B₁), CLOS, exact."""
    thm = M.inf_egal_produit_invariant()
    cible = impl(et(inf_egal_card(var("A"), var("A1")), inf_egal_card(var("B"), var("B1"))),
                 inf_egal_card(E.produit(var("A"), var("B")),
                               E.produit(var("A1"), var("B1"))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


def test_inf_egal_produit_invariant_non_tautologie():
    """Anti-tautologie : l'antécédent (≤ des facteurs) n'est pas le conséquent
    (≤ du produit)."""
    thm = M.inf_egal_produit_invariant()
    ante, cons = thm.conclusion.sous
    assert ante != cons


def test_inf_egal_produit_invariant_termes():
    """Tient quand les facteurs sont des TERMES composés (produits) — la version
    cardinaux (3) couvre le cas Card· via une généralisation/instanciation propre
    (le terme produit τ-libre évite la collision α des τ-cardinaux dans le graphe)."""
    A0 = E.produit(var("P"), var("Q"))
    thm = M.inf_egal_produit_invariant("F", "G", A0, var("B"), A0, var("B1"))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0


def test_cardinal_inf_egal_produit_invariant_clos():
    """Version cardinaux — ⊢ (Card A ≤ Card A₁ et Card B ≤ Card B₁) ⇒
    (Card A × Card B ≤ Card A₁ × Card B₁), CLOS."""
    thm = M.cardinal_inf_egal_produit_invariant()
    cible = impl(et(inf_egal_card(cardinal(var("A")), cardinal(var("A1"))),
                    inf_egal_card(cardinal(var("B")), cardinal(var("B1")))),
                 inf_egal_card(E.produit(cardinal(var("A")), cardinal(var("B"))),
                               E.produit(cardinal(var("A1")), cardinal(var("B1")))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


def test_inf_egal_produit_gauche_clos():
    """Facteur droit fixe — ⊢ (A ≤ A₁) ⇒ (A×C ≤ A₁×C), CLOS, exact."""
    thm = M.inf_egal_produit_gauche()
    cible = impl(inf_egal_card(var("A"), var("A1")),
                 inf_egal_card(E.produit(var("A"), var("C")),
                               E.produit(var("A1"), var("C"))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


def test_inf_egal_produit_droite_clos():
    """Facteur gauche fixe — ⊢ (B ≤ B₁) ⇒ (C×B ≤ C×B₁), CLOS, exact."""
    thm = M.inf_egal_produit_droite()
    cible = impl(inf_egal_card(var("B"), var("B1")),
                 inf_egal_card(E.produit(var("C"), var("B")),
                               E.produit(var("C"), var("B1"))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


def test_facteur_fixe_non_tautologie():
    """Anti-tautologie pour les versions à facteur fixe."""
    g = M.inf_egal_produit_gauche()
    d = M.inf_egal_produit_droite()
    assert g.conclusion.sous[0] != g.conclusion.sous[1]
    assert d.conclusion.sous[0] != d.conclusion.sous[1]
