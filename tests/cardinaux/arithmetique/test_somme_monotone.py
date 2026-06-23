"""Tests — §III.3.2-3.3 : monotonie de ≤ pour la somme + successeur croissant
(ensembles_somme_monotone).

  • inf_egal_somme_invariant : (A≤B₁ et B≤N₁) ⇒ (A⊔B ≤ B₁⊔N₁)  (somme d'injections) ;
  • inf_egal_monotone_successeur : (A≤B) ⇒ (A⊔{∅} ≤ B⊔{∅})  (successeur croissant) ;
  • cardinal_inf_egal_monotone_successeur : (Card A≤Card B) ⇒ (a+1 ≤ b+1).
Chaque test vérifie la conclusion EXACTE + clôture.
"""
from bourbaki.logique.formule import var, egal, et, inclus, impl
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.cardinaux.arithmetique import ensembles_somme_monotone as M
from bourbaki.cardinaux.arithmetique import ensembles_somme_equipotence as S


def _K():
    return S._somme_graphe("F", "G", "A", "B", "k")


def test_somme_graphe_image_inclus():
    """{F func,dom F=A,F⟨A⟩⊂B₁,G func,dom G=B,G⟨B⟩⊂N₁} ⊢ image(K,A⊔B) ⊂ B₁⊔N₁."""
    t = M.somme_graphe_image_inclus()
    AB = somme_disjointe(var("A"), var("B"))
    B1N1 = somme_disjointe(var("B1"), var("N1"))
    assert t.conclusion == inclus(E.image(_K(), AB), B1N1)
    # conditionnel : 4 hypothèses (dom F=A, dom G=B, F⟨A⟩⊂B₁, G⟨B⟩⊂N₁)
    assert len(t.hypotheses) == 4


def test_inf_egal_somme_invariant():
    """⊢ (A ≤ B₁ et B ≤ N₁) ⇒ (A ⊔ B ≤ B₁ ⊔ N₁)  (monotonie de la somme pour ≤)."""
    t = M.inf_egal_somme_invariant()
    AB = somme_disjointe(var("A"), var("B"))
    B1N1 = somme_disjointe(var("B1"), var("N1"))
    cible = impl(et(inf_egal_card(var("A"), var("B1")), inf_egal_card(var("B"), var("N1"))),
                 inf_egal_card(AB, B1N1))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_inf_egal_monotone_successeur():
    """⊢ (A ≤ B) ⇒ (A ⊔ {∅} ≤ B ⊔ {∅})  (le successeur cardinal est croissant)."""
    t = M.inf_egal_monotone_successeur("A", "B")
    SING = E.singleton(E.VIDE)
    AS = somme_disjointe(var("A"), SING)
    BS = somme_disjointe(var("B"), SING)
    cible = impl(inf_egal_card(var("A"), var("B")), inf_egal_card(AS, BS))
    assert t.conclusion == cible
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_cardinal_inf_egal_monotone_successeur():
    """⊢ (Card A ≤ Card B) ⇒ (Card A ⊔ {∅} ≤ Card B ⊔ {∅})  (= « a≤b ⇒ a+1≤b+1 »)."""
    t = M.cardinal_inf_egal_monotone_successeur("A", "B")
    SING = E.singleton(E.VIDE)
    cA, cB = cardinal(var("A")), cardinal(var("B"))
    cible = impl(inf_egal_card(cA, cB),
                 inf_egal_card(somme_disjointe(cA, SING), somme_disjointe(cB, SING)))
    assert t.conclusion == cible
    assert t.est_clos
