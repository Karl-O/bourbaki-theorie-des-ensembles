"""Chap. I §3.5 — L'équivalence, niveau assemblages (E I.30).

« A ⇔ B » est une ABRÉVIATION définie à partir de « et » (§3.4) et de ⇒.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, implication)
from bourbaki.i_description_mathematique_formelle.i_3_theories_logiques.i_3_4_conjonction import (
    conjonction)


# @livre Ch.I §3.5 Def.- | E I.30 L.34-37 | PDF p.30  (« A ⇔ B » désigne l'assemblage (A ⇒ B) et (B ⇒ A))
def equivalence(p: Assemblage, q: Assemblage) -> Assemblage:
    """A ⇔ B := (A ⇒ B) et (B ⇒ A). E I.30 (§I.3.5)."""
    return conjonction(implication(p, q), implication(q, p))


__all__ = ["equivalence"]
