"""Tests — §III.3.2 : ORDRE STRICT des petits cardinaux (ensembles_ordre_strict_petits).

Énoncé Bourbaki (E.III.3.2) : x < y :⇔ (x ≤ y et x ≠ y).  On certifie ici les
deux instances concrètes 0 < 1 et 1 < 2.  Chaque test vérifie que la conclusion
certifiée par le noyau EST EXACTEMENT la cible Bourbaki (inf_strict_card / inf_egal_card
/ ¬(·=·)), et la clôture (théorème inconditionnel : aucune hypothèse).
"""
from bourbaki.logique.formule import egal, non
from bourbaki.cardinaux import ensembles_ordre_strict_petits as S
from bourbaki.cardinaux.ensembles_cardinaux import (inf_egal_card, inf_strict_card)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import ZERO, UN, DEUX, successeur
from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
from bourbaki.ensembles import ensembles_abrege as E


_UNSOMME = somme_disjointe(UN, E.singleton(E.VIDE))   # 1 ⊔ {∅}   ;   2 = Card(1 ⊔ {∅})


# ═══════════════════════════════════════════════════════════════════════════════
# (1)  0 < 1
# ═══════════════════════════════════════════════════════════════════════════════
def test_zero_inf_egal_un():
    """⊢ 0 ≤ 1   (= inf_egal_card(0, 1) ; application vide ∅ → 1)."""
    t = S.zero_inf_egal_un()
    assert t.conclusion == inf_egal_card(ZERO, UN)
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_zero_distinct_un():
    """⊢ ¬(0 = 1)   (= 0 ≠ 1 ; 1 = successeur(0))."""
    t = S.zero_distinct_un()
    assert t.conclusion == non(egal(ZERO, UN))
    # 1 = successeur(0)  par définition (Ent.UN)
    assert t.conclusion == non(egal(ZERO, successeur(ZERO)))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_zero_strict_un():
    """⊢ 0 < 1   (ORDRE STRICT, E.III.3.2 ; = inf_strict_card(0, 1))."""
    t = S.zero_strict_un()
    assert t.conclusion == inf_strict_card(ZERO, UN)
    assert t.est_clos
    assert t.hypotheses == frozenset()


# ═══════════════════════════════════════════════════════════════════════════════
# (2)  1 < 2
# ═══════════════════════════════════════════════════════════════════════════════
def test_somme_inf_egal_deux():
    """⊢ (1 ⊔ {∅}) ≤ 2   (le SET 1⊔{∅} s'injecte dans son cardinal 2)."""
    t = S.somme_inf_egal_deux()
    assert t.conclusion == inf_egal_card(_UNSOMME, DEUX)
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_un_inf_egal_deux():
    """⊢ 1 ≤ 2   (= inf_egal_card(1, 2) ; transitivité 1 ≤ (1⊔{∅}) ≤ 2)."""
    t = S.un_inf_egal_deux()
    assert t.conclusion == inf_egal_card(UN, DEUX)
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_un_distinct_deux():
    """⊢ ¬(1 = 2)   (= 1 ≠ 2 ; 2 = successeur(1))."""
    t = S.un_distinct_deux()
    assert t.conclusion == non(egal(UN, DEUX))
    # 2 = successeur(1)  par définition (Ent.DEUX)
    assert t.conclusion == non(egal(UN, successeur(UN)))
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_un_strict_deux():
    """⊢ 1 < 2   (ORDRE STRICT, E.III.3.2 ; = inf_strict_card(1, 2))."""
    t = S.un_strict_deux()
    assert t.conclusion == inf_strict_card(UN, DEUX)
    assert t.est_clos
    assert t.hypotheses == frozenset()
