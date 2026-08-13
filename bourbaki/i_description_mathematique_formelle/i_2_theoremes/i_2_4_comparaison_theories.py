"""Chap. I §2.4 — Comparaison des théories (E I.24) : plus forte, équivalentes, C4, C5.

C4 et C5 sont des MÉTATHÉORÈMES (« hors fragment objet », cf. criteres_C.py) :
prose + démonstration en commentaire ; le cœur combinatoire de la définition
« plus forte » est rendu vérifiable sur des PRÉSENTATIONS FINIES de théories,
sans créer de ``Theoreme`` du noyau.
"""
from __future__ import annotations

from collections.abc import Callable, Collection, Sequence

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_1_assemblage import (
    Assemblage)


# @livre Ch.I §2.4 Def.- | E I.24 L.3-6 | PDF p.24  (titre §4 + théorie PLUS FORTE : signes ⊆, axiomes → théorèmes, schémas ⊆)
def est_plus_forte(signes: Collection[str], schemas: Collection[str],
                   axiomes: Sequence[Assemblage],
                   signes_p: Collection[str], schemas_p: Collection[str],
                   est_theoreme_p: Callable[[Assemblage], bool]) -> bool:
    """𝒯' plus forte que 𝒯 (E I.24 L.4-6), sur des présentations finies.

    Trois conditions : tous les signes de 𝒯 sont des signes de 𝒯' ; tous les
    axiomes explicites de 𝒯 sont des théorèmes de 𝒯' (décidé ici par le
    certificat `est_theoreme_p` fourni par l'appelant, p. ex. une démonstration
    couche 0 ou un `Theoreme` du noyau) ; les schémas de 𝒯 sont des schémas
    de 𝒯' (comparés par identifiant, p. ex. "S1".."S7").
    """
    return (set(signes) <= set(signes_p)
            and set(schemas) <= set(schemas_p)
            and all(est_theoreme_p(a) for a in axiomes))


# @livre Ch.I §2.4 Meta.4 | E I.24 L.7-14 | PDF p.24
#
# C4 (MÉTATHÉORÈME). « Si une théorie 𝒯' est plus forte qu'une théorie 𝒯,
# tous les théorèmes de 𝒯 sont des théorèmes de 𝒯'. »
#
# DÉMONSTRATION (livre, L.9-14). Soit R₁, ..., Rₙ une démonstration de 𝒯.
# On voit de proche en proche que chaque Rᵢ est un théorème de 𝒯'. Supposons
# l'assertion établie pour les relations précédant Rₖ. Si Rₖ est un axiome de
# 𝒯, c'est un théorème de 𝒯' par hypothèse (axiome explicite → théorème par
# définition de « plus forte » ; axiome implicite → formé par un schéma de 𝒯,
# qui est un schéma de 𝒯'). Si Rₖ est précédée par des relations Rᵢ et
# Rᵢ ⇒ Rₖ, on sait déjà que Rᵢ et Rᵢ ⇒ Rₖ sont des théorèmes de 𝒯', donc Rₖ
# est un théorème de 𝒯' d'après C1 (syllogisme).  ∎

# @livre Ch.I §2.4 Def.- | E I.24 L.15-17 | PDF p.24  (théories ÉQUIVALENTES : chacune plus forte que l'autre)
def sont_equivalentes(signes: Collection[str], schemas: Collection[str],
                      axiomes: Sequence[Assemblage],
                      est_theoreme: Callable[[Assemblage], bool],
                      signes_p: Collection[str], schemas_p: Collection[str],
                      axiomes_p: Sequence[Assemblage],
                      est_theoreme_p: Callable[[Assemblage], bool]) -> bool:
    """𝒯 et 𝒯' équivalentes (E I.24 L.15-17) : chacune est plus forte que l'autre.

    Conséquence (livre) : tout théorème de 𝒯 est un théorème de 𝒯' et
    vice-versa (par C4, appliqué dans les deux sens).
    """
    return (est_plus_forte(signes, schemas, axiomes,
                           signes_p, schemas_p, est_theoreme_p)
            and est_plus_forte(signes_p, schemas_p, axiomes_p,
                               signes, schemas, est_theoreme))


# @livre Ch.I §2.4 Meta.5 | E I.24 L.18-25 | PDF p.24
#
# C5 (MÉTATHÉORÈME). « Soient 𝒯 une théorie, A₁, ..., Aₙ ses axiomes
# explicites, a₁, ..., a_h ses constantes, T₁, ..., T_h des termes de 𝒯.
# Supposons que (T₁|a₁)(T₂|a₂)...(T_h|a_h)Aᵢ (pour i = 1, ..., n) soient des
# théorèmes d'une théorie 𝒯', que les signes de 𝒯 soient des signes de 𝒯' et
# que les schémas de 𝒯 soient des schémas de 𝒯'. Alors, si A est un théorème
# de 𝒯, (T₁|a₁)...(T_h|a_h)A est un théorème de 𝒯'. »
#
# DÉMONSTRATION (livre, L.24-25). 𝒯' est plus forte que la théorie
# (T₁|a₁)...(T_h|a_h)𝒯, et il suffit d'appliquer C2 puis C4.  ∎
#
# C'est C5 qui fonde « appliquer dans 𝒯' les résultats de 𝒯 » (les MODÈLES :
# substituer aux constantes de 𝒯 des termes de 𝒯' qui en vérifient les axiomes).

# @livre Ch.I §2.4 Rem.- | E I.24 L.26-39 | PDF p.24
#   (petits textes : « appliquer les résultats de 𝒯 dans 𝒯' », exemple du
#    modèle de la théorie des groupes dans la théorie des ensembles — prose)
# @livre Ch.I §2.4 Rem.- | E I.24 L.40-41 | PDF p.24
#   (sous les hypothèses de C5, si 𝒯 est contradictoire, 𝒯' l'est aussi —
#    la démonstration continue en E I.25, déjà annotée)

__all__ = ["est_plus_forte", "sont_equivalentes"]
