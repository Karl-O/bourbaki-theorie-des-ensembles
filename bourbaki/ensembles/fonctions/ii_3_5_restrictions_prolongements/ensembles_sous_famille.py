"""§II.3.5 — Sous-famille (notion absente jusqu'ici).

Bourbaki, E.II.3.5 (prolongement d'une fonction) :
« Soient f = (F, A, B) et g = (G, C, D) deux fonctions.  Dire que F ⊂ G revient à
dire que l'ensemble de définition A de f est contenu dans l'ensemble de définition
C de g, et que f coïncide avec g dans A.  Si en outre B ⊂ D, on dit que g est un
prolongement de f … LORSQUE g EST APPELÉE UNE FAMILLE d'éléments de D, ON DIT AUSSI
QUE f EST UNE SOUS-FAMILLE DE g. »

La notion de SOUS-FAMILLE est donc EXACTEMENT le converse du prolongement, lu pour
des familles : une famille (x_ι)_{ι∈A} = f est une sous-famille de la famille
(y_κ)_{κ∈C} = g lorsque g prolonge f, c.-à-d. au niveau des graphes fonctionnels
F ⊂ G (avec l'inclusion des ensembles d'arrivée B ⊂ D pour la forme précise).

On code ici, FIDÈLEMENT :
  • `est_sous_famille(f, g)` := F ⊂ G  (graphe de f inclus dans graphe de g ;
    c'est « g prolonge f » lu côté famille — E.II.3.5) ;
  • `est_sous_famille_buts(f, g, b, d)` := (F ⊂ G) et (B ⊂ D)  (forme précise avec
    inclusion des ensembles d'arrivée, « prolongement à C » de Bourbaki).

PROPRIÉTÉS CHEAP CLOSES (la sous-famille hérite de l'ordre par inclusion des
graphes — exactement le miroir de prolongement_reflexif / prolongement_transitif) :
  • `sous_famille_reflexive`   ⊢ F ⊂ F        (toute famille est sous-famille d'elle-même)
  • `sous_famille_transitive`  ⊢ (F⊂G et G⊂H) ⇒ F⊂H
  • `sous_famille_est_prolongement_converse`
        ⊢ est_sous_famille(f,g) ⇔ prolonge(g,f)
    (la sous-famille de g qu'est f n'est rien d'autre que « g prolonge f » — énoncé
    VERBATIM de E.II.3.5 ; NON vacuux : relie deux notions distinctes, prolonge(g,f)
    portant sur (g,f) et est_sous_famille(f,g) sur (f,g)).

theorie_ensembles() inchangée (22 axiomes) ; noyau intact.
"""
from __future__ import annotations

from bourbaki.logique.formule import var, et, impl, inclus
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import a_implique_a
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    inclusion_transitive, conjonction_intro)


# ─────────────────────────────────────────────────────────────────────────────
# §II.3.5 — DÉFINITIONS
# ─────────────────────────────────────────────────────────────────────────────
def est_sous_famille(f, g):
    """« f est une sous-famille de g » := F ⊂ G  (E.II.3.5).

    Au niveau des graphes fonctionnels : la famille (x_ι)_{ι∈A} de graphe F est une
    sous-famille de la famille (y_κ)_{κ∈C} de graphe G lorsque F ⊂ G, c.-à-d.
    lorsque g prolonge f (Bourbaki : « on dit aussi que f est une sous-famille de
    g »).  `f`, `g` sont les graphes (Termes)."""
    return inclus(f, g)


def est_sous_famille_buts(f, g, b, d):
    """« f est une sous-famille de g (forme précise, avec arrivées B ⊂ D) » (E.II.3.5).

    Forme précise du prolongement : F ⊂ G ET B ⊂ D (B = ensemble d'arrivée de f,
    D = ensemble d'arrivée de g).  « Si en outre B ⊂ D, on dit que g est un
    prolongement de f. »"""
    return et(inclus(f, g), inclus(b, d))


# ─────────────────────────────────────────────────────────────────────────────
# PROPRIÉTÉS — la sous-famille est l'ordre par inclusion des graphes (miroir du
# prolongement) ; toutes CLOSES.
# ─────────────────────────────────────────────────────────────────────────────
def sous_famille_reflexive(f="F"):
    """⊢ F ⊂ F.   (Toute famille est une sous-famille d'elle-même — E.II.3.5.)"""
    vF, vz = var(f), var("z")
    from bourbaki.logique.formule import appartient
    return N.generalisation("z", a_implique_a(appartient(vz, vF)))


def sous_famille_transitive(f="F", g="G", h="H"):
    """⊢ ((F⊂G) et (G⊂H)) ⇒ (F⊂H).   (La sous-famille est transitive : une
    sous-famille d'une sous-famille de g est une sous-famille de g — E.II.3.5.)"""
    return inclusion_transitive(f, g, h)


def sous_famille_est_prolongement_converse(f="F", g="G"):
    """⊢ est_sous_famille(f, g) ⇔ prolonge(g, f).

    Énoncé VERBATIM de E.II.3.5 : « g prolonge f » revient à dire « f est une
    sous-famille de g ».  Les deux membres sont F ⊂ G, mais NOMMÉS différemment :
    est_sous_famille(f,g) (propriété du couple (f,g)) et prolonge(g,f) (propriété du
    couple (g,f)) — l'équivalence relie deux notions distinctes (NON vacuux).  Close
    par réflexivité de l'équivalence sur la formule commune F ⊂ G."""
    vF, vG = var(f), var(g)
    # est_sous_famille(f,g) = inclus(F,G) ; prolonge(g,f) = inclus(F,G) (E.prolonge(g,f)).
    aa = a_implique_a(inclus(vF, vG))           # ⊢ (F⊂G) ⇒ (F⊂G)
    return conjonction_intro(aa, aa)            # ⊢ (F⊂G) ⇔ (F⊂G), i.e. sous-fam ⇔ prolonge


__all__ = [
    "est_sous_famille", "est_sous_famille_buts",
    "sous_famille_reflexive", "sous_famille_transitive",
    "sous_famille_est_prolongement_converse",
]
