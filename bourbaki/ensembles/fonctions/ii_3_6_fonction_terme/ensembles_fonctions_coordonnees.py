"""§II.3.6, Exemple 2 — Première et seconde FONCTIONS coordonnée sur G (notion
auparavant ABSENTE au niveau des applications).

⚠️ À NE PAS CONFONDRE avec `ensembles_projections.pr1/pr2` (les TERMES pr₁z, pr₂z,
coordonnées d'un couple z) ni avec `ensembles_abrege.pr1/pr2` : ici on définit les
APPLICATIONS (fonctions) z ↦ pr₁z et z ↦ pr₂z sur un ensemble G de couples.

Bourbaki, E.II.3.6 (Exemple 2) :
« Soit G un ensemble de couples.  Les fonctions z ↦ pr₁z (z∈G, pr₁z∈pr₁G) et
z ↦ pr₂z (z∈G, pr₂z∈pr₂G) s'appellent respectivement la première et la seconde
fonction coordonnée sur G ; on les désigne par pr₁ et pr₂ quand il n'en résulte
pas de confusion. »

Pour un ensemble de couples G, pr₁G = ensemble des premières coordonnées = dom(G),
pr₂G = ensemble des secondes coordonnées = img(G)  (E.II.38).  On code donc, via la
fonction définie par un terme `fonction_terme` (x↦T, E.II.46) :

  • `premiere_fonction_coordonnee(G)` := z ↦ pr₁z (z∈G, pr₁z∈pr₁G)
        = fonction_terme(G, pr₁z, dom(G)) ;
  • `seconde_fonction_coordonnee(G)`  := z ↦ pr₂z (z∈G, pr₂z∈pr₂G)
        = fonction_terme(G, pr₂z, img(G)).

PROPRIÉTÉS CHEAP CLOSES (C54, le graphe d'une fonction définie par un terme est
fonctionnel — `graphe_terme_fonctionnel`) :
  • `premiere_coordonnee_fonctionnelle`  ⊢ le graphe de pr₁ (sur G) est fonctionnel ;
  • `seconde_coordonnee_fonctionnelle`    ⊢ le graphe de pr₂ (sur G) est fonctionnel.

theorie_ensembles() inchangée (22 axiomes) ; noyau intact.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    graphe_terme_fonctionnel)


# ─────────────────────────────────────────────────────────────────────────────
# §II.3.6, Exemple 2 — DÉFINITIONS (applications sur G)
# ─────────────────────────────────────────────────────────────────────────────
# Liant par défaut de la variable parcourant G (« z » chez Bourbaki).  On prend
# « c0 » (pour « couple ») afin d'éviter toute COLLISION avec les liants internes
# réservés u, v, z, y du Critère C54 (graphe_terme_fonctionnel) : le NOM du liant
# est mathématiquement indifférent (renommage α), seule la notation de prose reste « z ».
_LIANT_COUPLE = "c0"


# @livre Ch.II §3.6 Ex.2 | E II.16 L.18-21 | PDF p.67
def premiere_fonction_coordonnee(g, z=_LIANT_COUPLE):
    """Première fonction coordonnée sur G : z ↦ pr₁z (z∈G, pr₁z∈pr₁G)  (E.II.3.6, Ex 2).

    `g` = ensemble de couples G (Terme).  Renvoie l'application (Terme triple
    (F, G, pr₁G)) de graphe {(z, pr₁z) | z∈G}, ensemble de définition G et ensemble
    d'arrivée pr₁G = dom(G)  (= ensemble des premières coordonnées des couples de G).
    Le terme T = pr₁z a `z` (par défaut « c0 ») pour variable libre (liant de x↦T)."""
    vz = var(z)
    return E.fonction_terme(g, E.pr1(vz), E.dom(g), z)


# @livre Ch.II §3.6 Ex.2 | E II.16 L.18-21 | PDF p.67
def seconde_fonction_coordonnee(g, z=_LIANT_COUPLE):
    """Seconde fonction coordonnée sur G : z ↦ pr₂z (z∈G, pr₂z∈pr₂G)  (E.II.3.6, Ex 2).

    `g` = ensemble de couples G (Terme).  Renvoie l'application (Terme triple
    (F, G, pr₂G)) de graphe {(z, pr₂z) | z∈G}, ensemble de définition G et ensemble
    d'arrivée pr₂G = img(G)  (= ensemble des secondes coordonnées des couples de G)."""
    vz = var(z)
    return E.fonction_terme(g, E.pr2(vz), E.img(g), z)


# ─────────────────────────────────────────────────────────────────────────────
# PROPRIÉTÉS — le graphe de chaque fonction coordonnée est FONCTIONNEL (C54)
# ─────────────────────────────────────────────────────────────────────────────
# @livre Ch.II §3.6 Crit.54 | E II.16 L.18-21 | PDF p.67
def premiere_coordonnee_fonctionnelle(g="G", z=_LIANT_COUPLE):
    """⊢ le graphe de la première fonction coordonnée sur G est fonctionnel  (C54).

    Le graphe est graphe_terme(G, pr₁z) ; sa fonctionnalité est le cœur du Critère
    C54 (`graphe_terme_fonctionnel`) : une fonction définie par un terme a au plus
    une valeur par antécédent.  (T = pr₁z, liant « c0 » ≠ liants internes u,v,z,y.)"""
    vG, vz = var(g), var(z)
    return graphe_terme_fonctionnel(vG, E.pr1(vz), z, "y")


# @livre Ch.II §3.6 Crit.54 | E II.16 L.18-21 | PDF p.67
def seconde_coordonnee_fonctionnelle(g="G", z=_LIANT_COUPLE):
    """⊢ le graphe de la seconde fonction coordonnée sur G est fonctionnel  (C54).
    (T = pr₂z, liant « c0 ».)"""
    vG, vz = var(g), var(z)
    return graphe_terme_fonctionnel(vG, E.pr2(vz), z, "y")


__all__ = [
    "premiere_fonction_coordonnee", "seconde_fonction_coordonnee",
    "premiere_coordonnee_fonctionnelle", "seconde_coordonnee_fonctionnelle",
]
