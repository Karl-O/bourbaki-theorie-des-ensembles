"""Chap. I §4.1 — Définition des quantificateurs (E I.32), niveau assemblages.

(∃x) et (∀x) ne sont PAS des signes primitifs : ce sont des abréviations
construites avec τ et la substitution (E I.32 L.1-6). La lettre x ne figure pas
dans τ_x(R), donc pas non plus dans (∃x)R ni (∀x)R.

Le §4.1 contient aussi deux méta-critères de substitution (CS8, CS9 — mêmes
statut et vérification que CS1-CS5 du §1.2 : identités d'assemblages) et les
critères C26/C27 (C27 = la primitive `generalisation` du noyau).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, lettres, negation, substitution_b_x_a as sub, tau_x)


# @livre Ch.I §4.1 Def.- | E I.32 L.1-6 | PDF p.32  (quantificateurs ∃ et ∀, abréviations sur τ)
def existe(x: str, r: Assemblage) -> Assemblage:
    """(∃x)R := (τ_x(R) | x) R.  E I.32 L.1-2."""
    return sub(tau_x(r, x), x, r)


def pour_tout(x: str, r: Assemblage) -> Assemblage:
    """(∀x)R := ¬(∃x)(¬R).  E I.32 L.2-3."""
    return negation(existe(x, negation(r)))


# @livre Ch.I §4.1 Crit.8 | E I.32 L.7-11 | PDF p.32  (CS8 : énoncé L.7-8, démo L.9-11 via CS1+CS3)
def cs8(r: Assemblage, x: str, xp: str) -> bool:
    """x'∉R ⟹ (∃x)R = (∃x')R' et (∀x)R = (∀x')R', où R' = (x'|x)R."""
    if xp in lettres(r):
        raise ValueError("CS8 exige x' ∉ R")
    rp = sub(Assemblage((xp,)), x, r)
    return (existe(x, r) == existe(xp, rp)
            and pour_tout(x, r) == pour_tout(xp, rp))


# @livre Ch.I §4.1 Crit.9 | E I.32 L.12-18 | PDF p.32  (CS9 : énoncé L.12-14, démo L.15-18 via CS2+CS4)
def cs9(r: Assemblage, u: Assemblage, x: str, y: str) -> bool:
    """x≠y, x∉U ⟹ (U|y)(∃x)R = (∃x)R' et (U|y)(∀x)R = (∀x)R', où R' = (U|y)R."""
    if x == y or x in lettres(u):
        raise ValueError("CS9 exige x≠y et x∉U")
    rp = sub(u, y, r)
    return (sub(u, y, existe(x, r)) == existe(x, rp)
            and sub(u, y, pour_tout(x, r)) == pour_tout(x, rp))


# @livre Ch.I §4.1 Rem.- | E I.32 L.22-26 | PDF p.32
#   (sens intuitif de (∃x)R / (∀x)R — prose, rien à formaliser)
# @livre Ch.I §4.1 Rem.- | E I.32 L.27-32 | PDF p.32
#   ((∃x)R comme théorème de légitimation de la méthode de la constante
#    auxiliaire (E I.28) — prose ; la méthode elle-même est au §3.3)

# @livre Ch.I §4.1 Crit.26 | E I.32 L.33-36 | PDF p.32  (C26 : énoncé L.33-34, démo L.35-36)
def c26_identite(r: Assemblage, x: str) -> bool:
    """Cœur ASSEMBLAGE de C26 : (∀x)R est IDENTIQUE à non non (τ_x(non R) | x)R.

    C26 (livre) : « (∀x)R et (τ_x(non R)|x)R sont équivalentes dans 𝒯. »
    Démonstration du livre : (∀x)R est identique à non((τ_x(non R)|x)(non R)),
    c.-à-d. — la substitution commutant avec ¬ (CS5) — à non non((τ_x(non R)|x)R) ;
    l'ÉQUIVALENCE dans 𝒯 s'obtient alors par double négation (C24, déposé au §3.5).
    Ici on vérifie l'identité d'assemblages, qui est la partie métamathématique.
    """
    corps = sub(tau_x(negation(r), x), x, r)
    return pour_tout(x, r) == negation(negation(corps))


# C27 (E I.32 L.37-39) : « si R est un théorème et x n'est pas une constante,
# (∀x)R est un théorème » — c'est la primitive de confiance `generalisation`
# du noyau (voir i_2_theoremes/noyau/noyau.py, marqueur @livre sur place).

__all__ = ["existe", "pour_tout", "cs8", "cs9", "c26_identite"]
