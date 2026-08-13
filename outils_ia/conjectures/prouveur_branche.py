"""L'adaptateur qui rend la trichotomie CAPABLE DE TRANCHER.

────────────────────────────────────────────────────────────────────────────────
LE DÉFAUT QU'IL RÉPARE, MESURÉ.  Sans prouveur injecté, `classer_residu.classer`
ne peut ni décharger ni réfuter : il ne lui reste que la réfutation par schéma et
le critère syntaxique.  Conséquence mesurée le 5 août 2026 : il rendait
« inconnu » pour Goldbach — mais AUSSI pour `z = z` et pour `4 = 2+2`, qui sont
vrais par construction.  Le verdict ne portait donc aucune information : il ne
distinguait pas l'ouvert du trivialement clos.

⚠️ On avait d'abord lu ce « inconnu » sur Goldbach comme un jugement honnête sur
un problème ouvert.  Il n'en était pas un : c'était la réponse par défaut du
classifieur à tout ce qu'il ne réfute pas.  Un verdict n'informe que si l'outil
qui le rend est capable d'en rendre un autre.

────────────────────────────────────────────────────────────────────────────────
POURQUOI UN ADAPTATEUR ET PAS UN BRANCHEMENT DIRECT.  `outils_ia.ia.prouveur_goal.
prouver` rend un couple `(Theoreme|None, nœuds explorés)` et prend ses hypothèses
en second argument ; `classer` attend `prouveur(cible, T0) -> Theoreme|None`.  Les
deux contrats sont incompatibles, ce qui explique que personne ne l'ait branché.

`classer` re-vérifie de toute façon ce qui sort — type, clôture, conclusion — donc
un adaptateur ne peut pas affaiblir la soundness : au pire il rend None.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Formule, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (
    noyau_abrege as N,
)

#: budget de nœuds du prouveur goal-directed, volontairement modeste : cet outil
#: sert à SÉPARER le trivial de l'ouvert, pas à chercher des preuves profondes.
NOEUDS_MAX = 2000
PROFONDEUR_MAX = 4


def _par_reflexivite(cible: Formule):
    """T = T par la primitive de réflexivité du noyau (Théorème 1, E I.39)."""
    if cible.tag != "=" or cible.termes[0] != cible.termes[1]:
        return None
    return N.reflexivite(cible.termes[0])


def _par_axiome(cible: Formule, T0):
    """La cible EST un axiome explicite de T0 : la règle `axiome` la rend close."""
    try:
        return N.axiome(T0, cible)
    except Exception:                                     # noqa: BLE001
        return None


def _par_recherche(cible: Formule):
    """Le prouveur goal-directed du dépôt, dont on jette le compteur de nœuds."""
    try:
        from outils_ia.ia.prouveur_goal import prouver
        resultat = prouver(cible, profondeur_max=PROFONDEUR_MAX,
                           noeuds_max=NOEUDS_MAX)
    except Exception:                                     # noqa: BLE001
        return None
    theoreme = resultat[0] if isinstance(resultat, tuple) else resultat
    return theoreme


def prouveur(cible: Formule, T0):
    """Le contrat qu'attend `classer` : un `Theoreme` CLOS de conclusion `cible`,
    ou `None`.

    Trois tentatives, de la moins chère à la plus chère.  Aucune n'est un oracle :
    `classer` re-vérifie le type, la clôture et la conclusion de ce qui sort, si
    bien qu'un adaptateur fautif fait perdre une preuve, jamais gagner un faux
    théorème."""
    for tentative in (lambda: _par_reflexivite(cible),
                      lambda: _par_axiome(cible, T0),
                      lambda: _par_recherche(cible)):
        try:
            th = tentative()
        except Exception:                                 # noqa: BLE001
            continue
        if isinstance(th, N.Theoreme) and th.est_clos and th.conclusion == cible:
            return th
    return None


__all__ = ["prouveur", "NOEUDS_MAX", "PROFONDEUR_MAX"]
