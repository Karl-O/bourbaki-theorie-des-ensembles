"""Tests — §III.3.4 : PROPOSITION 7 (produit cardinal non nul), forme binaire.

Énoncé Bourbaki (E.III.3.4, Prop 7, cas à deux indices) :
    a · b ≠ 0  ⟺  (a ≠ 0  et  b ≠ 0),      donc a·b = 0 ⟺ (a=0 ou b=0).
Ici 0 = Card(∅), a·b = Card(A×B).  On certifie les deux formes (« nul » et « non
nul ») et le lemme-clé Card X = 0 ⟺ X = ∅.  Chaque test vérifie la conclusion
EXACTE et la clôture.
"""
from bourbaki.logique.formule import var, egal, ou, non, et, equiv, impl
from bourbaki.cardinaux import ensembles_cardinaux_props_restantes_prop7 as P7
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


def test_equipotent_vide_implique_vide():
    """⊢ Eq(X, ∅) ⇒ (X = ∅)   (seul le vide est équipotent au vide)."""
    t = P7.equipotent_vide_implique_vide("X")
    assert t.conclusion == impl(equipotent(var("X"), E.VIDE), egal(var("X"), E.VIDE))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_egal_zero_ssi_vide():
    """⊢ (Card X = Card ∅) ⟺ (X = ∅)   (« a = 0 ⟺ a vide » ; lemme-clé Prop 7)."""
    t = P7.cardinal_egal_zero_ssi_vide("X")
    assert t.conclusion == equiv(egal(cardinal(var("X")), cardinal(E.VIDE)),
                                 egal(var("X"), E.VIDE))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_prop7_produit_nul():
    """⊢ (Card(A×B)=Card∅) ⟺ (CardA=Card∅ ou CardB=Card∅)   (a·b=0 ⟺ a=0 ou b=0)."""
    t = P7.prop7_produit_nul("A", "B")
    AB = E.produit(var("A"), var("B"))
    cAB0 = egal(cardinal(AB), cardinal(E.VIDE))
    cA0 = egal(cardinal(var("A")), cardinal(E.VIDE))
    cB0 = egal(cardinal(var("B")), cardinal(E.VIDE))
    assert t.conclusion == equiv(cAB0, ou(cA0, cB0))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_prop7_produit_non_nul():
    """⊢ ¬(Card(A×B)=Card∅) ⟺ (¬(CardA=Card∅) et ¬(CardB=Card∅))   (PROPOSITION 7)."""
    t = P7.prop7_produit_non_nul("A", "B")
    AB = E.produit(var("A"), var("B"))
    cAB0 = egal(cardinal(AB), cardinal(E.VIDE))
    cA0 = egal(cardinal(var("A")), cardinal(E.VIDE))
    cB0 = egal(cardinal(var("B")), cardinal(E.VIDE))
    assert t.conclusion == equiv(non(cAB0), et(non(cA0), non(cB0)))
    assert t.est_clos
    assert t.hypotheses == frozenset()
