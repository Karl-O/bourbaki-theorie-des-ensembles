"""Chap. I §3.4 — La conjonction, niveau assemblages (E I.29).

« A et B » est une ABRÉVIATION définie à partir de ¬ et ∨.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, negation, disjonction)


# @livre Ch.I §3.4 Def.- | E I.29 L.11-13 | PDF p.29  (« A et B » désigne l'assemblage non((non A) ou (non B)))
# @livre Ch.I §3.4 Rem.- | E I.29 L.36-36 | PDF p.29  (convention « A et B et C », « A ou B ou C » — début, prose)
# @livre Ch.I §3.4 Rem.- | E I.30 L.1-7 | PDF p.30  (suite : conjonctions multiples de proche en proche ; théorème ssi chaque Aᵢ est un théorème — prose)
# @livre Ch.I §3.4 Meta.- | E I.30 L.8-33 | PDF p.30  (métathéorème en petit texte : toute théorie logique équivaut à une théorie à au plus un axiome explicite ; réduction à 𝒯₀ — prose + preuve, JAMAIS un Theoreme du noyau)
def conjonction(p: Assemblage, q: Assemblage) -> Assemblage:
    """A et B := ¬((¬A) ∨ (¬B)). E I.29 (§I.3.4)."""
    return negation(disjonction(negation(p), negation(q)))


__all__ = ["conjonction"]
