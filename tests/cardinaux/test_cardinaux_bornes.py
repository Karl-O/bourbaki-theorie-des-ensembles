"""Tests — §III.3.2 : bornes de l'ordre ≤ des cardinaux (ensembles_cardinaux_bornes).

Énoncé Bourbaki (E.III.3.2) : « On a 0 ≤ x pour tout cardinal x, et 1 ≤ x pour
tout cardinal x ≠ 0. »  On certifie ici 0 ≤ a (application vide) et a ≤ a+1
(injection canonique gauche u↦(u,0)).  Chaque test vérifie que la conclusion
certifiée par le noyau EST EXACTEMENT la cible Bourbaki, et la clôture.
"""
from bourbaki.logique.formule import var, egal, inclus, impl, appartient
from bourbaki.cardinaux import ensembles_cardinaux_bornes as B
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E


# ── (1)  0 ≤ a  : l'application vide injecte ∅ dans A ─────────────────────────
def test_vide_injective_sur_vide():
    """⊢ injective_dans(∅, ∅)  (vacuement : aucun couple dans ∅)."""
    t = B.vide_injective_sur_vide()
    assert t.conclusion == E.injective_dans(E.VIDE, E.VIDE)
    assert t.est_clos


def test_image_vide_inclus():
    """⊢ image(∅, ∅) ⊂ A  (image du vide = ∅, inclus partout)."""
    t = B.image_vide_inclus("A")
    assert t.conclusion == inclus(E.image(E.VIDE, E.VIDE), var("A"))
    assert t.est_clos


def test_zero_inf_egal():
    """⊢ ∅ ≤ A   (« 0 ≤ a », E.III.3.2 ; témoin = graphe vide)."""
    t = B.zero_inf_egal("A")
    assert t.conclusion == inf_egal_card(E.VIDE, var("A"))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_zero_inf_egal():
    """⊢ Card(∅) ≤ Card(A)   (« 0 ≤ a » sur les cardinaux, E.III.3.2)."""
    t = B.cardinal_zero_inf_egal("A")
    assert t.conclusion == inf_egal_card(cardinal(E.VIDE), cardinal(var("A")))
    assert t.est_clos


# ── (2)  a ≤ a+1  : injection canonique gauche  u ↦ (u,0)  de A dans A⊔{∅} ─────
def _F():
    return B._F(var("A"))


def test_gauche_fonctionnel():
    """⊢ est_fonctionnel(F),  F = graphe de u↦(u,0)  (C54)."""
    t = B.gauche_fonctionnel("A")
    assert t.conclusion == E.est_fonctionnel(_F())
    assert t.est_clos


def test_gauche_domaine():
    """⊢ dom(F) = A  (l'injection gauche est définie sur tout A)."""
    t = B.gauche_domaine("A")
    assert t.conclusion == egal(E.dom(_F()), var("A"))
    assert t.est_clos


def test_gauche_valeur():
    """⊢ (u∈A) ⇒ F(u) = (u,0)  (la valeur de l'injection gauche en u)."""
    t = B.gauche_valeur("A", "u")
    cible = impl(appartient(var("u"), var("A")),
                 egal(E.valeur(_F(), var("u")), E.couple(var("u"), E.VIDE)))
    assert t.conclusion == cible
    assert t.est_clos


def test_gauche_injective():
    """⊢ injective_dans(F, A)  (u↦(u,0) est injective sur A)."""
    t = B.gauche_injective("A")
    assert t.conclusion == E.injective_dans(_F(), var("A"))
    assert t.est_clos


def test_gauche_image_inclus():
    """⊢ image(F, A) ⊂ A⊔{∅}  (l'image de l'injection gauche reste dans la somme)."""
    t = B.gauche_image_inclus("A")
    S = somme_disjointe(var("A"), E.singleton(E.VIDE))
    assert t.conclusion == inclus(E.image(_F(), var("A")), S)
    assert t.est_clos


def test_inf_egal_successeur():
    """⊢ A ≤ A⊔{∅}   (« a ≤ a+1 », E.III.3.2 / III.4.1)."""
    t = B.inf_egal_successeur("A")
    S = somme_disjointe(var("A"), E.singleton(E.VIDE))
    assert t.conclusion == inf_egal_card(var("A"), S)
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_inf_egal_successeur():
    """⊢ Card(A) ≤ Card(A)⊔{∅}   (« a ≤ a+1 » sur les cardinaux, E.III.3.2)."""
    t = B.cardinal_inf_egal_successeur("A")
    cA = cardinal(var("A"))
    assert t.conclusion == inf_egal_card(cA, somme_disjointe(cA, E.singleton(E.VIDE)))
    assert t.est_clos
