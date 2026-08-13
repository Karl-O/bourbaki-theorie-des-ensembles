"""Chap. I §2.3 — Substitutions dans une théorie (E I.23-24) : (T|x)𝒯, C2, C3.

C2 et C3 sont des MÉTATHÉORÈMES (démontrés sur le formalisme, pas dans une
théorie) : leur démonstration est consignée en commentaire, et leur cœur
vérifiable est rendu exécutable au niveau « couche 0 » (assemblages +
démonstrations de i_2_2_demonstration), SANS créer de ``Theoreme`` du noyau.
"""
from __future__ import annotations

from collections.abc import Collection, Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, lettres, substitution_b_x_a as sub)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.i_2_2_demonstration import (
    est_demonstration)


# @livre Ch.I §2.3 Def.- | E I.23 L.18-22 | PDF p.23  (la théorie (T|x)𝒯 : mêmes signes et schémas, axiomes substitués)
def theorie_substituee(axiomes: Sequence[Assemblage], x: str,
                       t: Assemblage) -> tuple[Assemblage, ...]:
    """Les axiomes explicites de (T|x)𝒯 : (T|x)A₁, ..., (T|x)Aₙ (E I.23 L.20-22).

    (T|x)𝒯 a par définition les mêmes signes et les mêmes schémas que 𝒯 ;
    seule la liste des axiomes explicites change.
    """
    return tuple(sub(t, x, a) for a in axiomes)


# @livre Ch.I §2.3 Meta.2 | E I.23 L.23-33 | PDF p.23
#
# C2 (MÉTATHÉORÈME). « Soient A un théorème d'une théorie 𝒯, T un terme de 𝒯,
# x une lettre. Alors (T|x)A est un théorème de (T|x)𝒯. »
#
# DÉMONSTRATION (livre, L.25-33). Soit R₁, ..., Rₙ une démonstration de 𝒯 où
# figure A. La suite (T|x)R₁, ..., (T|x)Rₙ est une suite de relations de 𝒯
# d'après CF8 (E I.20). C'est une démonstration de (T|x)𝒯 : si Rₖ est un axiome
# implicite de 𝒯, (T|x)Rₖ en est encore un (E I.22, condition b des schémas),
# donc de (T|x)𝒯 ; si Rₖ est un axiome explicite de 𝒯, (T|x)Rₖ est un axiome
# explicite de (T|x)𝒯 ; enfin si Rₖ est précédée des relations Rᵢ et Rⱼ, Rⱼ
# étant Rᵢ ⇒ Rₖ, alors (T|x)Rₖ est précédée de (T|x)Rᵢ et de (T|x)Rⱼ, et cette
# dernière est identique à (T|x)Rᵢ ⇒ (T|x)Rₖ (critère CS5).  ∎
#
# Pas un `Theoreme` du noyau — mais le cœur de la preuve est VÉRIFIABLE sur le
# fragment couche 0 (axiomes explicites + détachement) :
def c2_sur_demonstration(suite: Sequence[Assemblage],
                         axiomes: Collection[Assemblage],
                         x: str, t: Assemblage) -> bool:
    """Rejoue C2 sur une démonstration CONCRÈTE (fragment sans schémas).

    Vérifie que l'image (T|x)R₁, ..., (T|x)Rₙ d'une démonstration de 𝒯 est
    bien une démonstration de (T|x)𝒯 — exactement l'argument du livre,
    l'étape « détachement » étant couverte par CS5.
    """
    if not est_demonstration(suite, axiomes):
        raise ValueError("la suite donnée n'est pas une démonstration")
    image = [sub(t, x, r) for r in suite]
    return est_demonstration(image, theorie_substituee(tuple(axiomes), x, t))


# @livre Ch.I §2.3 Def.- | E I.21 L.31-33 | PDF p.21  (constantes = lettres des axiomes explicites)
def constantes(axiomes: Sequence[Assemblage]) -> frozenset[str]:
    """Les constantes de 𝒯 : lettres figurant dans les axiomes explicites (E I.21 L.31-33)."""
    out: set[str] = set()
    for a in axiomes:
        out.update(lettres(a))
    return frozenset(out)


# @livre Ch.I §2.3 Meta.3 | E I.23 L.34-37 | PDF p.23
# @livre Ch.I §2.3 Rem.- | E I.24 L.1-2 | PDF p.24
#
# C3 (MÉTATHÉORÈME). « Soient A un théorème d'une théorie 𝒯, T un terme de 𝒯,
# et x une lettre qui n'est pas une constante de 𝒯. Alors (T|x)A est un
# théorème de 𝒯. »
#
# DÉMONSTRATION (livre, L.36-37). Cela résulte aussitôt de C2, puisque x ne
# figure pas dans les axiomes explicites de 𝒯 : (T|x)Aᵢ est identique à Aᵢ,
# donc (T|x)𝒯 est 𝒯 elle-même.  ∎
# (E I.24 L.1-2 : si les axiomes explicites ne contiennent pas de lettres —
#  ou s'il n'y en a pas — C3 s'applique sans restriction sur x.)
def c3_sans_constante(axiomes: Sequence[Assemblage], x: str,
                      t: Assemblage) -> bool:
    """Cœur vérifiable de C3 : x ∉ constantes ⟹ (T|x)𝒯 a les MÊMES axiomes que 𝒯."""
    if x in constantes(axiomes):
        raise ValueError("C3 exige que x ne soit pas une constante de la théorie")
    return theorie_substituee(tuple(axiomes), x, t) == tuple(axiomes)


__all__ = ["theorie_substituee", "c2_sur_demonstration",
           "constantes", "c3_sans_constante"]
