"""Tests §III.3/4 — Vers « 0 + 1 = 1 » : singletons équipotents + somme ∅ ⊔ {∅}.

Vérifie (conclusion EXACTE + est_clos) :
  • le graphe constant C:{a}→{b} est une bijection (4 conjoints) ;
  • eq_singletons          ⊢ Eq({a}, {b}) ;
  • somme_zero_un_egale_singleton ⊢ ∅⊔{∅} = {(∅,1)} ;
  • eq_somme_zero_un       ⊢ Eq(∅⊔{∅}, {∅}) ;
  • card_somme_zero_un     ⊢ Card(∅⊔{∅}) = Card({∅})   (= « 0+1 = 1 » au niveau cardinal).
"""
from formule import var, egal
import ensembles_abrege as E
from ensembles_cardinaux import equipotent, cardinal, est_bijection_de
from ensembles_somme_disjointe import somme_disjointe, somme_cardinale_binaire, UN
from ensembles_zero_plus_un import (
    const_graphe_fonctionnel, const_graphe_domaine, const_graphe_valeur,
    const_graphe_injective, const_graphe_image, const_est_bijection,
    eq_singletons, somme_zero_un_egale_singleton, membre_singleton_vide,
    eq_somme_zero_un, card_somme_zero_un, _const_graphe)


def test_const_graphe_conjoints():
    """Les 4 conjoints du graphe constant C:{a}→{b} sont clos."""
    assert const_graphe_fonctionnel("a", "b").est_clos
    assert const_graphe_domaine("a", "b").est_clos
    assert const_graphe_injective("a", "b").est_clos
    assert const_graphe_image("a", "b").est_clos
    # image(C, {a}) = {b}  (conclusion exacte)
    C = _const_graphe("a", "b")
    assert const_graphe_image("a", "b").conclusion == egal(
        E.image(C, E.singleton(var("a"))), E.singleton(var("b")))


def test_const_est_bijection():
    """⊢ est_bijection_de(C, {a}, {b}) — bijection complète, conclusion exacte + clos."""
    thm = const_est_bijection("a", "b")
    assert thm.est_clos
    C = _const_graphe("a", "b")
    cible = est_bijection_de(C, E.singleton(var("a")), E.singleton(var("b")))
    assert thm.conclusion == cible


def test_eq_singletons():
    """⊢ Eq({a}, {b}) — deux singletons sont équipotents, conclusion exacte + clos."""
    thm = eq_singletons("a", "b")
    assert thm.est_clos
    assert thm.conclusion == equipotent(E.singleton(var("a")), E.singleton(var("b")))


def test_membre_singleton_vide():
    """⊢ ∅ ∈ {∅} — clos."""
    assert membre_singleton_vide().est_clos


def test_somme_zero_un_egale_singleton():
    """⊢ (∅ ⊔ {∅}) = {(∅, 1)} — égalité d'ensembles, conclusion exacte + clos."""
    vide = E.VIDE
    sing = E.singleton(vide)
    AB = somme_disjointe(vide, sing)
    scpl = E.singleton(E.couple(vide, UN))
    thm = somme_zero_un_egale_singleton()
    assert thm.est_clos
    assert thm.conclusion == egal(AB, scpl)


def test_eq_somme_zero_un():
    """⊢ Eq(∅ ⊔ {∅}, {∅}) — « 0+1 = 1 » ensembliste, conclusion exacte + clos."""
    vide = E.VIDE
    sing = E.singleton(vide)
    AB = somme_disjointe(vide, sing)
    thm = eq_somme_zero_un()
    assert thm.est_clos
    assert thm.conclusion == equipotent(AB, sing)


def test_card_somme_zero_un():
    """⊢ Card(∅ ⊔ {∅}) = Card({∅}) — « 0+1 = 1 » CARDINAL, conclusion exacte + clos.

    Card(∅⊔{∅}) EST somme_cardinale_binaire(∅, {∅}) = « 0 + 1 » (définition E.III.3.3) ;
    Card({∅}) = « 1 ».  C'est l'égalité 0 + 1 = 1 comme cardinaux de ces ensembles."""
    vide = E.VIDE
    sing = E.singleton(vide)
    AB = somme_disjointe(vide, sing)
    thm = card_somme_zero_un()
    assert thm.est_clos
    assert thm.conclusion == egal(cardinal(AB), cardinal(sing))
    # fidélité : Card(∅⊔{∅}) est BIEN la somme cardinale binaire « 0 + 1 »
    assert cardinal(AB) == somme_cardinale_binaire(vide, sing)
