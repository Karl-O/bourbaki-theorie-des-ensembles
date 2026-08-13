"""Chap. I §5 — Théories égalitaires : l'assemblage T = U, niveau assemblages.

« = » est un signe relationnel de poids 2 (E I.38) ; l'assemblage T = U
s'écrit en notation préfixe « = » ++ T ++ U.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import Assemblage, concat


# @livre Ch.I §5.1 Def.- | E I.38 L.14-19 | PDF p.38  (théorie égalitaire : signe = de poids 2 ; l'assemblage = TU est la relation d'égalité, désignée T = U)
def egalite(t: Assemblage, u: Assemblage) -> Assemblage:
    """T = U := l'assemblage « = » ++ T ++ U (= signe relationnel, poids 2). E I.38 (§I.5)."""
    return concat(concat(Assemblage(("=",)), t), u)


__all__ = ["egalite"]
