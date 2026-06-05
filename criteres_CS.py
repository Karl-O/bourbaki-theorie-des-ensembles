"""Critères de substitution CS1–CS5 (Bourbaki §I.1.2).

Ce sont des MÉTA-critères : des identités d'assemblages sur les opérateurs
(B|x) et τ_x. Contrairement aux C-critères, ils ne sont pas des théorèmes du
noyau mais des PROPRIÉTÉS de la couche substitution — on les vérifie donc par
égalité d'assemblages (comme le round-trip de lecture). Ils justifient
métamathématiquement les manipulations utilisées partout ailleurs.

Énoncés (V7 §I.1.2, vérifiés verbatim) :
  CS1 : x'∉A ⟹ (B|x')(x'|x)A = (B|x)A
  CS2 : x≠y, y∉B ⟹ (B|x)(C|y)A = (C'|y)(B|x)A,  C'=(B|x)C
  CS3 : x'∉A ⟹ τ_x(A) = τ_x'(A'),  A'=(x'|x)A
  CS4 : x∉B, x≠y ⟹ (B|y)τ_x(A) = τ_x(A'),  A'=(B|y)A
  CS5 : (C|x) homomorphisme : (C|x)¬A=¬(C|x)A ; (C|x)(A∨B)=(C|x)A∨(C|x)B ;
        (C|x)(A⇒B)=(C|x)A⇒(C|x)B ; (C|x)(s A B)=s (C|x)A (C|x)B.
"""
from __future__ import annotations

from assemblage import (Assemblage, substitution_b_x_a as sub, tau_x, lettres,
                        negation, disjonction, implication, egalite)


def cs1(a, b, x, xp) -> bool:
    """x'∉A ⟹ (B|x')(x'|x)A = (B|x)A."""
    if xp in lettres(a):
        raise ValueError("CS1 exige x' ∉ A")
    return sub(b, xp, sub(Assemblage((xp,)), x, a)) == sub(b, x, a)


def cs2(a, b, c, x, y) -> bool:
    """x≠y, y∉B ⟹ (B|x)(C|y)A = ((B|x)C | y)(B|x)A."""
    if x == y or y in lettres(b):
        raise ValueError("CS2 exige x≠y et y∉B")
    cp = sub(b, x, c)
    return sub(b, x, sub(c, y, a)) == sub(cp, y, sub(b, x, a))


def cs3(a, x, xp) -> bool:
    """x'∉A ⟹ τ_x(A) = τ_x'((x'|x)A)."""
    if xp in lettres(a):
        raise ValueError("CS3 exige x' ∉ A")
    return tau_x(a, x) == tau_x(sub(Assemblage((xp,)), x, a), xp)


def cs4(a, b, x, y) -> bool:
    """x∉B, x≠y ⟹ (B|y)τ_x(A) = τ_x((B|y)A)."""
    if x == y or x in lettres(b):
        raise ValueError("CS4 exige x≠y et x∉B")
    return sub(b, y, tau_x(a, x)) == tau_x(sub(b, y, a), x)


def cs5_negation(a, c, x) -> bool:
    """(C|x)(¬A) = ¬(C|x)A."""
    return sub(c, x, negation(a)) == negation(sub(c, x, a))


def cs5_disjonction(a, b, c, x) -> bool:
    """(C|x)(A∨B) = (C|x)A ∨ (C|x)B."""
    return sub(c, x, disjonction(a, b)) == disjonction(sub(c, x, a), sub(c, x, b))


def cs5_implication(a, b, c, x) -> bool:
    """(C|x)(A⇒B) = (C|x)A ⇒ (C|x)B."""
    return sub(c, x, implication(a, b)) == implication(sub(c, x, a), sub(c, x, b))


def cs5_signe(t, u, c, x) -> bool:
    """(C|x)(= t u) = (= (C|x)t (C|x)u)  (signe spécifique = de poids 2)."""
    return sub(c, x, egalite(t, u)) == egalite(sub(c, x, t), sub(c, x, u))


__all__ = ["cs1", "cs2", "cs3", "cs4",
           "cs5_negation", "cs5_disjonction", "cs5_implication", "cs5_signe"]
