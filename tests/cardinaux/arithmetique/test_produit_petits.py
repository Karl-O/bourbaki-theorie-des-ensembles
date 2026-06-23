"""Tests — identités du produit cardinal avec 0 et 1 (a·1=a, a·0=0, §III.3.3)."""
from bourbaki.logique.formule import var, egal, et, appartient
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import cardinal, equipotent, est_bijection_de
from bourbaki.cardinaux.arithmetique.ensembles_produit_petits import (
    produit_vide_droit, produit_cardinal_zero,
    proj_graphe_fonctionnel, proj_graphe_domaine, proj_graphe_valeur,
    proj_graphe_injective, proj_graphe_image, proj_est_bijection,
    eq_produit_un, produit_cardinal_un)


def _concl(thm):
    return thm.conclusion


def _clos(thm):
    return len(thm.hypotheses) == 0


# ══════════════════════════ a·0 = 0 ══════════════════════════════════════════
def test_produit_vide_droit():
    """⊢ A×∅ = ∅  (clos)."""
    thm = produit_vide_droit("A")
    assert _clos(thm)
    assert _concl(thm) == egal(E.produit(var("A"), E.VIDE), E.VIDE)


def test_produit_cardinal_zero():
    """⊢ Card(A×∅) = Card(∅)   (a·0 = 0, clos)."""
    thm = produit_cardinal_zero("A")
    assert _clos(thm)
    assert _concl(thm) == egal(cardinal(E.produit(var("A"), E.VIDE)), cardinal(E.VIDE))


# ══════════════════════════ a·1 = a : la bijection ═══════════════════════════
def test_proj_graphe_fonctionnel():
    """⊢ P fonctionnel  (clos)."""
    thm = proj_graphe_fonctionnel("A")
    assert _clos(thm)


def test_proj_graphe_domaine():
    """⊢ dom P = A×{∅}  (clos)."""
    thm = proj_graphe_domaine("A")
    assert _clos(thm)
    A1 = E.produit(var("A"), E.singleton(E.VIDE))
    assert _concl(thm) == egal(E.dom(E.graphe_terme(A1, E.pr1(var("k"), "a", "b"), "k")), A1)


def test_proj_graphe_valeur():
    """{u∈A×{∅}} ⊢ P(u) = pr₁u."""
    thm = proj_graphe_valeur("A", "u")
    A1 = E.produit(var("A"), E.singleton(E.VIDE))
    P = E.graphe_terme(A1, E.pr1(var("k"), "a", "b"), "k")
    assert appartient(var("u"), A1) in thm.hypotheses
    assert _concl(thm) == egal(E.valeur(P, var("u")), E.pr1(var("u"), "a", "b"))


def test_proj_graphe_injective():
    """⊢ injective_dans(P, A×{∅})  (clos)."""
    thm = proj_graphe_injective("A")
    assert _clos(thm)


def test_proj_graphe_image():
    """⊢ image(P, A×{∅}) = A  (clos)."""
    thm = proj_graphe_image("A")
    assert _clos(thm)
    A1 = E.produit(var("A"), E.singleton(E.VIDE))
    P = E.graphe_terme(A1, E.pr1(var("k"), "a", "b"), "k")
    assert _concl(thm) == egal(E.image(P, A1), var("A"))


def test_proj_est_bijection():
    """⊢ est_bijection_de(P, A×{∅}, A)  (clos)."""
    thm = proj_est_bijection("A")
    assert _clos(thm)
    A1 = E.produit(var("A"), E.singleton(E.VIDE))
    P = E.graphe_terme(A1, E.pr1(var("k"), "a", "b"), "k")
    assert _concl(thm) == est_bijection_de(P, A1, var("A"))


def test_eq_produit_un():
    """⊢ Eq(A×{∅}, A)  (clos)."""
    thm = eq_produit_un("A")
    assert _clos(thm)
    A1 = E.produit(var("A"), E.singleton(E.VIDE))
    assert _concl(thm) == equipotent(A1, var("A"))


def test_produit_cardinal_un():
    """⊢ Card(A×{∅}) = Card(A)   (a·1 = a, clos)."""
    thm = produit_cardinal_un("A")
    assert _clos(thm)
    A1 = E.produit(var("A"), E.singleton(E.VIDE))
    assert _concl(thm) == egal(cardinal(A1), cardinal(var("A")))
