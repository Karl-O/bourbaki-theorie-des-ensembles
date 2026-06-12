"""Tests — §III.3.2-3.3 MONOTONIE de ≤ au niveau des CARDINAUX de la somme et du
produit (ensembles_cardinal_ordre_props).

Compléments « niveau cardinal » de la monotonie ENSEMBLISTE déjà close :
  • somme :   (A ≤ A₁ et B ≤ B₁) ⇒ Card(A⊔B) ≤ Card(A₁⊔B₁)  (additivité de ≤),
              + cas à SOMMANT FIXE (gauche/droite) ;
  • produit : (A ≤ A₁) ⇒ Card(A×C) ≤ Card(A₁×C)  et symétrique (facteur fixe).

Tout est obtenu par COMPOSITION de théorèmes déjà clos (inf_egal_somme_invariant /
inf_egal_produit_gauche / inf_egal_produit_droite ENSEMBLISTES, transportés par
inf_egal_transporte_cardinal : X ≤ Y ⇒ Card X ≤ Card Y).  Aucun axiome ajouté :
theorie=22.
"""
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.formule import var, et, impl
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
from bourbaki.cardinaux import ensembles_cardinal_ordre_props as P


def test_theorie_intangible_22():
    """La théorie des ensembles reste à 22 axiomes (rien postulé)."""
    assert len(E.theorie_ensembles().axiomes) == 22


# ── (1) ADDITIVITÉ de ≤ pour la somme cardinale ───────────────────────────────
def test_somme_cardinale_additive_clos():
    """⊢ (A ≤ A₁ et B ≤ B₁) ⇒ Card(A⊔B) ≤ Card(A₁⊔B₁), CLOS, conclusion EXACTE."""
    thm = P.somme_cardinale_additive()
    cible = impl(et(inf_egal_card(var("A"), var("A1")), inf_egal_card(var("B"), var("B1"))),
                 inf_egal_card(cardinal(somme_disjointe(var("A"), var("B"))),
                               cardinal(somme_disjointe(var("A1"), var("B1")))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


def test_somme_cardinale_additive_non_tautologie():
    """Anti-tautologie : l'antécédent (≤ des sommants) n'est pas le conséquent
    (≤ des cardinaux des sommes) ; et la conclusion n'est pas une hypothèse."""
    thm = P.somme_cardinale_additive()
    ante, cons = thm.conclusion.sous
    assert ante != cons
    assert thm.conclusion not in thm.hypotheses


# ── (2) version CARDINAUX (a≤a₁ et b≤b₁ ⇒ a+b ≤ a₁+b₁) ────────────────────────
def test_cardinal_inf_egal_somme_additive_clos():
    """⊢ (Card A ≤ Card A₁ et Card B ≤ Card B₁) ⇒
          Card(Card A ⊔ Card B) ≤ Card(Card A₁ ⊔ Card B₁), CLOS, EXACT."""
    thm = P.cardinal_inf_egal_somme_additive()
    cible = impl(et(inf_egal_card(cardinal(var("A")), cardinal(var("A1"))),
                    inf_egal_card(cardinal(var("B")), cardinal(var("B1")))),
                 inf_egal_card(cardinal(somme_disjointe(cardinal(var("A")), cardinal(var("B")))),
                               cardinal(somme_disjointe(cardinal(var("A1")), cardinal(var("B1"))))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


# ── (3) somme à sommant droit fixe ────────────────────────────────────────────
def test_somme_cardinale_monotone_gauche_clos():
    """⊢ (A ≤ A₁) ⇒ Card(A⊔C) ≤ Card(A₁⊔C), CLOS, EXACT."""
    thm = P.somme_cardinale_monotone_gauche()
    cible = impl(inf_egal_card(var("A"), var("A1")),
                 inf_egal_card(cardinal(somme_disjointe(var("A"), var("C"))),
                               cardinal(somme_disjointe(var("A1"), var("C")))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


# ── (4) somme à sommant gauche fixe ───────────────────────────────────────────
def test_somme_cardinale_monotone_droite_clos():
    """⊢ (B ≤ B₁) ⇒ Card(C⊔B) ≤ Card(C⊔B₁), CLOS, EXACT."""
    thm = P.somme_cardinale_monotone_droite()
    cible = impl(inf_egal_card(var("B"), var("B1")),
                 inf_egal_card(cardinal(somme_disjointe(var("C"), var("B"))),
                               cardinal(somme_disjointe(var("C"), var("B1")))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


# ── (5) produit à facteur droit fixe (niveau Card) ────────────────────────────
def test_produit_cardinale_monotone_gauche_clos():
    """⊢ (A ≤ A₁) ⇒ Card(A×C) ≤ Card(A₁×C), CLOS, EXACT."""
    thm = P.produit_cardinale_monotone_gauche()
    cible = impl(inf_egal_card(var("A"), var("A1")),
                 inf_egal_card(cardinal(E.produit(var("A"), var("C"))),
                               cardinal(E.produit(var("A1"), var("C")))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


# ── (6) produit à facteur gauche fixe (niveau Card) ───────────────────────────
def test_produit_cardinale_monotone_droite_clos():
    """⊢ (B ≤ B₁) ⇒ Card(C×B) ≤ Card(C×B₁), CLOS, EXACT."""
    thm = P.produit_cardinale_monotone_droite()
    cible = impl(inf_egal_card(var("B"), var("B1")),
                 inf_egal_card(cardinal(E.produit(var("C"), var("B"))),
                               cardinal(E.produit(var("C"), var("B1")))))
    assert thm.est_clos
    assert len(thm.hypotheses) == 0
    assert thm.conclusion == cible


# ── anti-tautologie pour les versions à facteur/sommant fixe ──────────────────
def test_facteur_sommant_fixe_non_tautologie():
    """Anti-tautologie : antécédent ≠ conséquent, conclusion ∉ hypothèses."""
    for thm in (P.somme_cardinale_monotone_gauche(), P.somme_cardinale_monotone_droite(),
                P.produit_cardinale_monotone_gauche(), P.produit_cardinale_monotone_droite()):
        ante, cons = thm.conclusion.sous
        assert ante != cons
        assert thm.conclusion not in thm.hypotheses
