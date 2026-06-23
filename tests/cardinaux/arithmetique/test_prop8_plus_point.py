"""Tests §III.3.4 — structure « + un point marqué » de A ⊔ {∅}
(briques certifiées du cœur back-and-forth de la Proposition 8).

Vérifie (conclusions EXACTES + clos) que l'ensemble augmenté A⊔{∅} est la copie de
gauche A×{0} à laquelle on adjoint, disjointement, l'unique point marqué * = (∅,1) :
  • marqueur_dans_somme        : (∅,1) ∈ A ⊔ {∅} ;
  • marqueur_hors_copie_gauche : ¬((∅,1) ∈ A×{0}) ;
  • somme_un_plus_point        : (z∈A⊔{∅}) ⇔ ((z∈A×{0}) ou (z=(∅,1))).
"""
from bourbaki.logique.i_1_termes_relations.formule import var, egal, ou, non, appartient, equiv
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe, ZERO, UN
from bourbaki.cardinaux.arithmetique import ensembles_prop8_plus_point as PP


_SING = E.singleton(E.VIDE)
_STAR = E.couple(E.VIDE, UN)


def _AS(t):
    return somme_disjointe(t, _SING)


def _A0(t):
    return E.produit(t, E.singleton(ZERO))


def test_marqueur():
    """Le point marqué * = (∅, 1)."""
    assert PP.marqueur() == _STAR


def test_marqueur_dans_somme():
    """⊢ (∅, 1) ∈ A ⊔ {∅}, CLOS."""
    A = var("A")
    t = PP.marqueur_dans_somme(A)
    assert t.conclusion == appartient(_STAR, _AS(A))
    assert t.est_clos


def test_marqueur_hors_copie_gauche():
    """⊢ ¬((∅, 1) ∈ A×{0}), CLOS  (la disjonction des copies : 1 ≠ 0)."""
    A = var("A")
    t = PP.marqueur_hors_copie_gauche(A)
    assert t.conclusion == non(appartient(_STAR, _A0(A)))
    assert t.est_clos


def test_somme_un_plus_point():
    """⊢ (z ∈ A⊔{∅}) ⇔ ((z ∈ A×{0}) ou (z = (∅,1))), CLOS."""
    A, z = var("A"), var("z")
    t = PP.somme_un_plus_point(A, "z")
    target = equiv(appartient(z, _AS(A)), ou(appartient(z, _A0(A)), egal(z, _STAR)))
    assert t.conclusion == target
    assert t.est_clos


def test_briques_cote_b():
    """Les briques sont paramétrées : elles valent identiquement pour le côté B, CLOS."""
    B = var("B")
    td = PP.marqueur_dans_somme(B)
    th = PP.marqueur_hors_copie_gauche(B)
    assert td.conclusion == appartient(_STAR, _AS(B))
    assert th.conclusion == non(appartient(_STAR, _A0(B)))
    assert td.est_clos and th.est_clos


def test_somme_un_plus_point_terme():
    """Robustesse : la décomposition tient quand A est un TERME composé (A = U×V), CLOS."""
    U, V = var("U"), var("V")
    AB = E.produit(U, V)
    t = PP.somme_un_plus_point(AB, "z")
    z = var("z")
    target = equiv(appartient(z, _AS(AB)), ou(appartient(z, _A0(AB)), egal(z, _STAR)))
    assert t.conclusion == target
    assert t.est_clos
