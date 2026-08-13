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

from bourbaki.i_description_mathematique_formelle.assemblage import (Assemblage, substitution_b_x_a as sub, tau_x, lettres,
                        negation, disjonction, implication, egalite,
                        conjonction, equivalence)


# @livre Ch.I §1.2 Rem.- | E I.16 L.35-38 | PDF p.16  (début du §1.2 : la mathématique formelle n'a que des assemblages explicites ; besoin de critères — prose)
# @livre Ch.I §1.2 Rem.- | E I.17 L.1-8 | PDF p.17
#   (intro : les critères décrivent une fois pour toutes des manipulations
#    d'assemblages ; leur justification appartient à la MÉTAMATHÉMATIQUE — prose)
# @livre Ch.I §1.2 Crit.1 | E I.17 L.9-10 | PDF p.17
def cs1(a, b, x, xp) -> bool:
    """x'∉A ⟹ (B|x')(x'|x)A = (B|x)A."""
    if xp in lettres(a):
        raise ValueError("CS1 exige x' ∉ A")
    return sub(b, xp, sub(Assemblage((xp,)), x, a)) == sub(b, x, a)


# @livre Ch.I §1.2 Crit.2 | E I.17 L.11-13 | PDF p.17
def cs2(a, b, c, x, y) -> bool:
    """x≠y, y∉B ⟹ (B|x)(C|y)A = ((B|x)C | y)(B|x)A."""
    if x == y or y in lettres(b):
        raise ValueError("CS2 exige x≠y et y∉B")
    cp = sub(b, x, c)
    return sub(b, x, sub(c, y, a)) == sub(cp, y, sub(b, x, a))


# @livre Ch.I §1.2 Crit.3 | E I.17 L.14-15 | PDF p.17
def cs3(a, x, xp) -> bool:
    """x'∉A ⟹ τ_x(A) = τ_x'((x'|x)A)."""
    if xp in lettres(a):
        raise ValueError("CS3 exige x' ∉ A")
    return tau_x(a, x) == tau_x(sub(Assemblage((xp,)), x, a), xp)


# @livre Ch.I §1.2 Crit.4 | E I.17 L.16-17 | PDF p.17
def cs4(a, b, x, y) -> bool:
    """x∉B, x≠y ⟹ (B|y)τ_x(A) = τ_x((B|y)A)."""
    if x == y or x in lettres(b):
        raise ValueError("CS4 exige x≠y et x∉B")
    return sub(b, y, tau_x(a, x)) == tau_x(sub(b, y, a), x)


# @livre Ch.I §1.2 Demo.- | E I.17 L.22-29 | PDF p.17
#   (principe de la vérification de CS2, en petit texte — la vérification
#    EXÉCUTABLE est cs2() ci-dessus, qui teste l'identité d'assemblages)
# @livre Ch.I §1.2 Crit.5 | E I.17 L.18-21 | PDF p.17
def cs5_negation(a, c, x) -> bool:
    """(C|x)(¬A) = ¬(C|x)A."""
    return sub(c, x, negation(a)) == negation(sub(c, x, a))


# @livre Ch.I §1.2 Crit.5 | E I.17 L.18-21 | PDF p.17
def cs5_disjonction(a, b, c, x) -> bool:
    """(C|x)(A∨B) = (C|x)A ∨ (C|x)B."""
    return sub(c, x, disjonction(a, b)) == disjonction(sub(c, x, a), sub(c, x, b))


# @livre Ch.I §1.2 Crit.5 | E I.17 L.18-21 | PDF p.17
def cs5_implication(a, b, c, x) -> bool:
    """(C|x)(A⇒B) = (C|x)A ⇒ (C|x)B."""
    return sub(c, x, implication(a, b)) == implication(sub(c, x, a), sub(c, x, b))


# @livre Ch.I §1.2 Crit.5 | E I.17 L.18-21 | PDF p.17
def cs5_signe(t, u, c, x) -> bool:
    """(C|x)(= t u) = (= (C|x)t (C|x)u)  (signe spécifique = de poids 2)."""
    return sub(c, x, egalite(t, u)) == egalite(sub(c, x, t), sub(c, x, u))


# ── CS6 et CS7 : substitution à travers les abréviateurs « et » / « ⇔ » ──────
# (énoncés aux §3.4 et §3.5, où Bourbaki introduit ces abréviations ; même
#  statut et même vérification que CS1-CS5 : identités d'assemblages, la démo
#  du livre étant « cela résulte de CS5 » — ici l'identité se VÉRIFIE.)

# @livre Ch.I §3.4 Crit.6 | E I.29 L.14-16 | PDF p.29
# @livre Ch.I §3.4 Demo.- | E I.29 L.14-16 | PDF p.29  (démo = dépliage de l'abréviation + CS5, vérifiée par l'identité exécutable)
def cs6(a, b, c, x) -> bool:
    """(C|x)(A et B) = (C|x)A et (C|x)B.

    « A et B » abrège ¬(¬A ∨ ¬B) : la substitution traverse l'abréviation
    (CS5 sur ¬ et ∨), d'où l'identité, vérifiée ici sur les assemblages."""
    return sub(c, x, conjonction(a, b)) == conjonction(sub(c, x, a), sub(c, x, b))


# @livre Ch.I §3.5 Crit.7 | E I.30 L.38-40 | PDF p.30
# @livre Ch.I §3.5 Demo.- | E I.30 L.38-40 | PDF p.30  (démo = dépliage de l'abréviation + CS5/CS6, vérifiée par l'identité exécutable)
def cs7(a, b, c, x) -> bool:
    """(C|x)(A ⇔ B) = (C|x)A ⇔ (C|x)B.

    « A ⇔ B » abrège (A⇒B) et (B⇒A) : mêmes raisons que CS6."""
    return sub(c, x, equivalence(a, b)) == equivalence(sub(c, x, a), sub(c, x, b))


__all__ = ["cs1", "cs2", "cs3", "cs4",
           "cs5_negation", "cs5_disjonction", "cs5_implication", "cs5_signe",
           "cs6", "cs7"]
