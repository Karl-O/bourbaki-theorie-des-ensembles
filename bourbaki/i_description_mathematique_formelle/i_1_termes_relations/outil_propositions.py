"""Couche 0 (bis) — atomes propositionnels : A⇒A est littéralement ∨¬AA.

Dans le fragment propositionnel (schémas S1–S4), les métavariables R, S, T
désignent des relations quelconques. Pour raisonner *directement* sur la forme
— sans instancier par une relation concrète comme (a=b) — on introduit des
**atomes propositionnels** : des signes relationnels de poids 0.

Convention : une seule lettre MAJUSCULE déclarée dans `SIG_PROP` est un atome
(une relation), les lettres minuscules restant des lettres-termes. La lecture
consulte la signature avant `est_lettre`, donc « A » est lu comme la relation
atomique A, et l'assemblage de A⇒A est exactement ∨ ¬ A A = (OU, NON, A, A).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import Assemblage
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_app_lecture import DEFAUT

# Atomes propositionnels disponibles (poids 0, sorte « relation »).
_NOMS = ("A", "B", "C", "D", "E")

SIG_PROP = dict(DEFAUT)
for _n in _NOMS:
    SIG_PROP[_n] = (0, "relation")


def atome(nom: str) -> Assemblage:
    """L'atome propositionnel `nom` comme assemblage de poids 0."""
    if nom not in SIG_PROP or SIG_PROP[nom][0] != 0:
        raise ValueError(f"atome propositionnel inconnu : {nom!r}")
    return Assemblage((nom,))


# Raccourcis prêts à l'emploi.
A, B, C, D, E = (atome(n) for n in _NOMS)


__all__ = ["SIG_PROP", "atome", "A", "B", "C", "D", "E"]
