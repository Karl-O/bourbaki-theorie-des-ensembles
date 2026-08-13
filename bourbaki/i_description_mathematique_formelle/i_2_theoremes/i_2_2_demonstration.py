"""Chap. I §2 — Théorèmes : axiomes et démonstrations, niveau assemblages (E I.21--25).

Au §2, Bourbaki définit un *texte démonstratif* puis une *démonstration* : une
suite de relations (assemblages) dont chaque terme est

  * soit un AXIOME de la théorie (§2.1) ;
  * soit se DÉDUIT de deux termes antérieurs R et R ⇒ S de la suite, dont il
    est le second membre S (règle du syllogisme / detachement, §2.2).

Un THÉORÈME est une relation qui figure dans une démonstration. Ce module est
la lecture « couche 0 » de cette définition : il ne CRÉE aucun ``Theoreme`` du
noyau (frontière de confiance intacte), il VÉRIFIE qu'une suite d'assemblages
est une démonstration. La version opératoire (noyau LCF, critères C1--C3 de
§2.3) vit à côté : ``noyau/`` + ``criteres/`` + ``tactiques/`` (ce paquet i_2_theoremes).
"""
from __future__ import annotations

from collections.abc import Collection, Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage, implication)


# @livre Ch.I §2 Rem.- | E I.21 L.23-27 | PDF p.21  (conventions d'écriture non(A), « ou », ⇒ — prose ; la couche notation les implémente)
# @livre Ch.I §2.2 Def.- | E I.22 L.24-25 | PDF p.22  (condition b : S, T antérieures avec T = S ⇒ R)
def se_deduit(s: Assemblage, anterieurs: Sequence[Assemblage]) -> bool:
    """True ssi S se déduit de deux termes antérieurs R et R ⇒ S (E I.22 L.24-25).

    On cherche R parmi les antérieurs tel que l'assemblage R ⇒ S y figure aussi.
    """
    vus = set(anterieurs)
    return any(implication(r, s) in vus for r in anterieurs)


# @livre Ch.I §2.2 Def.- | E I.22 L.16-25 | PDF p.22  (texte démonstratif 1°-2°, démonstration : conditions a₁, a₂, b)
def premiere_faute(suite: Sequence[Assemblage],
                   axiomes: Collection[Assemblage]) -> int | None:
    """Indice 0-based du premier terme ni axiome ni déduit ; None si démonstration.

    C'est le « vérificateur de texte démonstratif » : chaque terme doit être un
    axiome (§2.1) ou se déduire de deux termes antérieurs (§2.2).
    """
    ax = set(axiomes)
    for i, s in enumerate(suite):
        if s in ax:
            continue
        if se_deduit(s, suite[:i]):
            continue
        return i
    return None


def est_demonstration(suite: Sequence[Assemblage],
                      axiomes: Collection[Assemblage]) -> bool:
    """True ssi la suite est une démonstration dans la théorie d'axiomes donnés (E I.22 L.18-25)."""
    return len(suite) > 0 and premiere_faute(suite, axiomes) is None


# @livre Ch.I §2.2 Def.- | E I.22 L.26-26 | PDF p.22  (théorème = relation figurant dans une démonstration)
# @livre Ch.I §2.2 Rem.- | E I.22 L.27-38 | PDF p.22  (notion relative à l'état de la théorie ; « vraie », solution — prose)
# @livre Ch.I §2.2 Def.- | E I.22 L.39-41 | PDF p.22  (relation FAUSSE = ¬R théorème ; théorie CONTRADICTOIRE — prose, formalisé au §2.4 via C6/C7)
def est_theoreme(r: Assemblage, suite: Sequence[Assemblage],
                 axiomes: Collection[Assemblage]) -> bool:
    """True ssi R figure dans une démonstration de la théorie (E I.22 L.26).

    Bourbaki : « un théorème est une relation qui figure dans une démonstration ».
    On vérifie que la suite proposée EST une démonstration et que R y figure.
    """
    return est_demonstration(suite, axiomes) and r in tuple(suite)


__all__ = ["se_deduit", "premiere_faute", "est_demonstration", "est_theoreme"]
