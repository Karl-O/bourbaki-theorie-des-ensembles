"""Tactiques sur le noyau ABRÉGÉ + premiers théorèmes du chapitre II.

Les dérivations sont IDENTIQUES à celles du niveau τ (⇒ y est aussi ¬∨), donc
le portage est direct. On démarre par le strict nécessaire à la réflexivité de
l'inclusion ; le reste de la boîte à outils suivra.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, appartient, inclus
from bourbaki.logique import noyau_abrege as N


def antecedent_consequent(f):
    """Décompose une implication A⇒B (= ¬A ∨ B) en (A, B)."""
    if not (f.tag == "ou" and f.sous[0].tag == "non"):
        raise ValueError("pas une implication ¬A ∨ B")
    return f.sous[0].sous[0], f.sous[1]


def a_implique_a(a):
    """⊢ A ⇒ A.  (assume A, décharge.)"""
    return N.loi_deduction(a, N.assume(a))


def syllogisme(thm_ab, thm_bc):
    """⊢ A⇒B, ⊢ B⇒C ⟹ ⊢ A⇒C."""
    a, _ = antecedent_consequent(thm_ab.conclusion)
    hc = N.modus_ponens(N.modus_ponens(N.assume(a), thm_ab), thm_bc)
    return N.loi_deduction(a, hc)


# ── Chapitre II — premier théorème : réflexivité de ⊂ ─────────────────────────

def inclusion_reflexive(x: str = "x"):
    """⊢ x ⊂ x.  (x⊂x = (∀z)(z∈x ⇒ z∈x) = généralisation de z∈x ⇒ z∈x.)"""
    z = "z" if x != "z" else "y"
    interne = a_implique_a(appartient(var(z), var(x)))     # ⊢ (z∈x) ⇒ (z∈x)
    return N.generalisation(z, interne)                    # ⊢ (∀z)(z∈x⇒z∈x) = (x⊂x)


__all__ = ["antecedent_consequent", "a_implique_a", "syllogisme",
           "inclusion_reflexive"]
