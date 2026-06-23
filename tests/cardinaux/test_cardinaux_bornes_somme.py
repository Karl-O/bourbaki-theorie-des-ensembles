"""Tests — §III.3.2 : bornes de la SOMME et du PRODUIT cardinal.

Énoncés Bourbaki (E.III.3.2) :  a ≤ a+b,  b ≤ a+b,  et  a ≤ a·b  (si b ≠ 0).
On certifie (symboliquement, A/B génériques) :
  • A ≤ A⊔B           (injection canonique gauche u↦(u,0)) ;
  • B ≤ A⊔B           (injection canonique droite  v↦(v,1)) ;
  • ¬(B=∅) ⇒ A ≤ A×B  (injection x↦(x,e), e∈B fixé).
Chaque test vérifie que la conclusion certifiée par le noyau EST EXACTEMENT la
cible Bourbaki, et la clôture.
"""
from bourbaki.logique.formule import var, non, egal
from bourbaki.cardinaux import ensembles_cardinaux_bornes_somme as B
from bourbaki.cardinaux.ensembles_cardinaux import (inf_egal_card, cardinal,
                               est_injection_de)
from bourbaki.cardinaux.arithmetique.ensembles_copie_marquee import _copie_graphe
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, ZERO, UN
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


# ── (1)  a ≤ a+b  : injection canonique gauche  u ↦ (u,0)  de A dans A⊔B ───────
def test_somme_gauche_injection():
    """⊢ est_injection_de(Δ_0, A, A⊔B)  (les 4 conjoints de l'injection gauche)."""
    t = B.somme_gauche_injection("A", "B")
    DX = _copie_graphe("A", ZERO)
    S = somme_disjointe(var("A"), var("B"))
    assert t.conclusion == est_injection_de(DX, var("A"), S)
    assert t.est_clos


def test_inf_egal_somme_gauche():
    """⊢ A ≤ A⊔B   (« a ≤ a+b », E.III.3.2 ; injection gauche)."""
    t = B.inf_egal_somme_gauche("A", "B")
    S = somme_disjointe(var("A"), var("B"))
    assert t.conclusion == inf_egal_card(var("A"), S)
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_inf_egal_somme_gauche():
    """⊢ Card(A) ≤ Card(A)⊔B   (« a ≤ a+b » sur les cardinaux, E.III.3.2)."""
    t = B.cardinal_inf_egal_somme_gauche("A", "B")
    cA = cardinal(var("A"))
    assert t.conclusion == inf_egal_card(cA, somme_disjointe(cA, var("B")))
    assert t.est_clos


# ── (2)  b ≤ a+b  : injection canonique droite  v ↦ (v,1)  de B dans A⊔B ───────
def test_somme_droite_injection():
    """⊢ est_injection_de(Δ_1, B, A⊔B)  (les 4 conjoints de l'injection droite)."""
    t = B.somme_droite_injection("A", "B")
    DX = _copie_graphe("B", UN)
    S = somme_disjointe(var("A"), var("B"))
    assert t.conclusion == est_injection_de(DX, var("B"), S)
    assert t.est_clos


def test_inf_egal_somme_droite():
    """⊢ B ≤ A⊔B   (« b ≤ a+b », E.III.3.2 ; injection droite)."""
    t = B.inf_egal_somme_droite("A", "B")
    S = somme_disjointe(var("A"), var("B"))
    assert t.conclusion == inf_egal_card(var("B"), S)
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_inf_egal_somme_droite():
    """⊢ Card(B) ≤ A⊔Card(B)   (« b ≤ a+b » sur les cardinaux, E.III.3.2)."""
    t = B.cardinal_inf_egal_somme_droite("A", "B")
    cB = cardinal(var("B"))
    assert t.conclusion == inf_egal_card(cB, somme_disjointe(var("A"), cB))
    assert t.est_clos


# ── (3)  a ≤ a·b  (si b ≠ 0)  : injection  x ↦ (x,e)  de A dans A×B ────────────
def test_produit_injection_temoin():
    """{m∈B} ⊢ est_injection_de(Δ_m, A, A×B)  (les 4 conjoints, témoin m)."""
    t = B.produit_injection_temoin("A", "m", "B")
    DX = _copie_graphe("A", var("m"))
    AB = E.produit(var("A"), var("B"))
    assert t.conclusion == est_injection_de(DX, var("A"), AB)
    # hypothèse résiduelle : m ∈ B
    from bourbaki.logique.formule import appartient
    assert t.hypotheses == frozenset({appartient(var("m"), var("B"))})


def test_inf_egal_produit():
    """⊢ ¬(B=∅) ⇒ (A ≤ A×B)   (« a ≤ a·b si b≠0 », E.III.3.2)."""
    from bourbaki.logique.formule import impl
    t = B.inf_egal_produit("A", "B")
    AB = E.produit(var("A"), var("B"))
    cible = impl(non(egal(var("B"), E.VIDE)), inf_egal_card(var("A"), AB))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_inf_egal_produit():
    """⊢ ¬(B=∅) ⇒ (Card(A) ≤ Card(A)×B)   (= a ≤ a·b si b≠0, sur les cardinaux)."""
    from bourbaki.logique.formule import impl
    t = B.cardinal_inf_egal_produit("A", "B")
    cA = cardinal(var("A"))
    AB = E.produit(cA, var("B"))
    cible = impl(non(egal(var("B"), E.VIDE)), inf_egal_card(cA, AB))
    assert t.conclusion == cible
    assert t.est_clos
