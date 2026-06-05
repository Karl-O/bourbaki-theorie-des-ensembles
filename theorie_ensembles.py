"""Chapitre II — Théorie des ensembles : ∈, ⊂ (et le MUR des quantificateurs τ).

Démarrage du chapitre II — qui révèle un mur ARCHITECTURAL, à documenter
honnêtement plutôt qu'à masquer.

MUR : ∃/∀ sont DÉFINIS par substitution de τ_x(R) (qui contient une copie de R) :
  (∃x)R := (τx(R)|x)R   →   chaque occurrence de x dans R est remplacée par τx(R).
Avec des quantificateurs imbriqués (comme dans A1, A2…), la taille de
l'assemblage développé EXPLOSE (multiplicative par niveau → exponentielle).
Concrètement, construire A1 = (∀x)(∀y)((x⊂y et y⊂x) ⇒ x=y) lève un MemoryError.

C'est FIDÈLE à Bourbaki (ses assemblages formels sont astronomiques — son « 1 »
≈ 10¹² signes ; cf. sa remarque §I.1 sur la nécessité pratique des abréviateurs).
Mais cela impose, pour le chapitre II, de représenter ∀/∃/Coll comme des
ABRÉVIATEURS de premier ordre (niveau arbre), NON développés en τ — une extension
du noyau (quantificateurs primitifs, la τ-expansion restant la justification).
Voir la note de relance dans la mémoire projet.

Ce module fournit donc seulement ce qui ne gonfle pas (∈, ⊂ à un seul niveau).
"""
from __future__ import annotations

from assemblage import (Assemblage, concat, implication, pour_tout)


def appartient(x: Assemblage, y: Assemblage) -> Assemblage:
    """x ∈ y  (signe relationnel 'in', poids 2). Ne gonfle pas."""
    return concat(concat(Assemblage(("in",)), x), y)


def inclus(x: Assemblage, y: Assemblage, z: str = "z") -> Assemblage:
    """x ⊂ y := (∀z)((z∈x) ⇒ (z∈y)).  Un seul niveau de quantificateur : OK."""
    zt = Assemblage((z,))
    return pour_tout(z, implication(appartient(zt, x), appartient(zt, y)))


# Énoncés A1, A2, Coll : volontairement NON construits ici (gonflement τ
# exponentiel → MemoryError). Ils nécessitent des quantificateurs abréviateurs
# (extension du noyau, à venir). Voir le docstring du module.

__all__ = ["appartient", "inclus"]
