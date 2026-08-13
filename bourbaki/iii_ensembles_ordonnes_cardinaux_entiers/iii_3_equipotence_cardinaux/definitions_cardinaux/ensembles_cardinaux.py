"""§III.3 — Ensembles équipotents. Cardinaux : définitions (abrégées).

Définitions VERBATIM de E.III.3 (énoncés lus dans le Texte.tex) :

  • Déf. 1 (Équipotence) : Eq(X, Y) :⇔ (∃F)(F est le graphe d'une bijection de X
    sur Y).  Comme dans tout le projet, une « bijection de X sur Y » est manipulée
    par son GRAPHE F : F est fonctionnel, dom F = X (F est partout définie sur X),
    F est injectif, et l'image directe F⟨X⟩ = Y (F est surjective sur Y).
    C'est l'implémentation §III.3.1 :  Eq(X,Y) :⇔ (∃f)(f bijection de X sur Y).

  • Déf. 2 (Cardinal) : Card(X) := τ_Z(Eq(X, Z))   (assemblage matriciel, l'opérateur
    τ_Z appliqué à la relation Eq(X, Z)).

  • Relation d'ordre ≤ entre cardinaux (Implémentation §III.3.2) :
        x ≤ y :⇔ (∃f)(f est une injection de x dans y),
    et x < y :⇔ (x ≤ y et x ≠ y).

  • Déf. 3-4 (somme/produit/exposant cardinaux) : encodées comme TERMES sur la
    somme disjointe / produit de famille / ensemble des applications, conformément
    au codage exact du Texte.tex.

Le prédicat `equipotent` est une « relation R{X,Y} » (fonction Python (Terme,
Terme)→Formule), comme pour les relations d'équivalence/d'ordre du projet : on peut
ainsi lui appliquer est_symetrique / est_transitive / est_relation_equivalence
(ensembles_abrege).  Les THÉORÈMES (réflexivité/symétrie/transitivité, ordre) sont
dans ensembles_equipotence.py.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, app, tau, egal, et, non, impl, existe, pourtout,
                     appartient, inclus)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E


# ── Déf. 1 : « F est le graphe d'une bijection de X sur Y » ────────────────────
def est_bijection_de(F, X, Y):
    """« F est le graphe d'une bijection de X sur Y » :=
       F fonctionnel ∧ dom F = X ∧ F injectif ∧ F⟨X⟩ = Y   (E.III.3.1, Déf. 1).

    Une application de X dans Y est codée (tout le projet) par son graphe F :
    fonctionnel et défini sur tout X.  « Bijective » ajoute injectivité et
    surjectivité (image directe F⟨X⟩ = Y), comme est_bijective de E.II.49."""
    return et(et(E.est_fonctionnel(F), egal(E.dom(F), X)),
              E.est_bijective(F, X, Y))


# @livre Ch.III §3.1 Def.1 | E III.23 L.15-17 | PDF p.126
def equipotent(X, Y):
    """Eq(X, Y) := (∃F)(F est le graphe d'une bijection de X sur Y)   (E.III.3.1, Déf. 1).

    Relation R{X,Y} : fonction (Terme,Terme)→Formule, utilisable avec
    est_symetrique / est_transitive / est_relation_equivalence."""
    return existe("F", est_bijection_de(var("F"), X, Y))


# ── Déf. 2 : Cardinal Card(X) = τ_Z(Eq(X, Z)) ─────────────────────────────────
# @livre Ch.III §3.1 Rem.- | E III.23 L.24-33 | PDF p.126
#   (paragraphe « De ce qui précède résulte … Posons la définition suivante : » —
#    S7 fournit τ_Z(Eq(X,Z)) = τ_Z(Eq(Y,Z)) pour X, Y équipotents ; c'est la
#    justification de la Déf. 2, couverte par cette définition ; prose.)
# @livre Ch.III §3.1 Def.2 | E III.23 L.34-35 | PDF p.126
def cardinal(X, z="Z"):
    """Card(X) := τ_Z(Eq(X, Z))   (cardinal / puissance de X, E.III.3.1, Déf. 2).

    Assemblage matriciel : l'opérateur formel τ_Z appliqué à Eq(X, Z)."""
    return tau(z, equipotent(X, var(z)))


# Exemples de cardinaux (E.III.3.1, Exemples) :  0 = Card(∅).
CARD_VIDE = cardinal(E.VIDE)          # 0 = Card(∅)  (= ∅, cf. Exemple 1)


def est_cardinal(a, x="X"):
    """« a est un cardinal » := (∃X)(a = Card(X))   (a est de la forme Card(X)).

    Bourbaki manipule « x est un cardinal » dans le Théorème 1 ; un cardinal est
    par définition un objet de la forme Card(X)."""
    vX = var(x)
    return existe(x, egal(a, cardinal(vX)))


# ── Relation d'ordre ≤ entre cardinaux (Implémentation §III.3.2) ───────────────
def est_injection_de(F, X, Y):
    """« F est le graphe d'une injection de X dans Y » :=
       F fonctionnel ∧ dom F = X ∧ F injective SUR X ∧ F⟨X⟩ ⊂ Y   (E.III.3.2).

    Application (graphe fonctionnel défini sur X) injective (au sens GARDÉ par X,
    « deux éléments de X » — fidèle à Bourbaki, cf. est_bijective), à valeurs dans
    Y (image directe incluse dans Y)."""
    return et(et(et(E.est_fonctionnel(F), egal(E.dom(F), X)),
                 E.injective_dans(F, X)),
              inclus(E.image(F, X), Y))


# @livre Ch.III §3.2 Rem.- | E III.25 L.4-6 | PDF p.128
#   (« Nous noterons x ≤ y la relation R{x,y}. Pour qu'un ensemble X soit équipotent
#    à une partie d'un ensemble Y, il faut et il suffit que Card(X) ≤ Card(Y). »)
def inf_egal_card(x, y):
    """x ≤ y :⇔ (∃f)(f est une injection de x dans y)   (E.III.3.2, Implémentation).

    Relation d'ordre entre cardinaux (Théorème 1)."""
    return existe("F", est_injection_de(var("F"), x, y))


def inf_strict_card(x, y):
    """x < y :⇔ (x ≤ y et x ≠ y)   (ordre strict entre cardinaux, E.III.3.2)."""
    return et(inf_egal_card(x, y), non(egal(x, y)))


# @livre Ch.III §3.2 Th.1 | E III.24 L.11-14 | PDF p.127
def relation_ordre_cardinaux(x, y):
    """R{x, y} du Théorème 1 : « x et y sont des cardinaux et x est équipotent à
       une partie de y », codée x≤y :⇔ (∃f)(f injection de x dans y) (E.III.3.2).

    Forme « R{x,y} » (fonction (Terme,Terme)→Formule), avec la garde « cardinaux »
    explicite, fidèle à l'énoncé du Théorème 1."""
    return et(et(est_cardinal(x), est_cardinal(y)), inf_egal_card(x, y))


# ── Déf. 3-4 : somme, produit, exposant de cardinaux ──────────────────────────
# @livre Ch.III §3.3 Def.3 | E III.25 L.45-48 | PDF p.128
# @livre Ch.III §3.3 Rem.- | E III.26 L.1-2 | PDF p.129
#   (prose : « on dit simplement "produit" et "somme" … et on écrit ∏ au lieu de P » ;
#    notation, rien à formaliser au-delà de la Déf. 3.)
def somme_cardinale(f, i):
    """∑_{ι∈I} a_ι := Card(⨆_{ι∈I} a_ι) = Card(somme de la famille)   (E.III.3.3, Déf. 3).

    Somme codée par la somme disjointe a_ι×{ι} (terme somme_famille)."""
    return cardinal(E.somme_famille(f, i))


# @livre Ch.III §3.3 Def.3 | E III.25 L.45-48 | PDF p.128
def produit_cardinal(f, i):
    """∏_{ι∈I} a_ι := Card(∏_{ι∈I} a_ι) = Card(produit de la famille)   (E.III.3.3, Déf. 3).

    Produit codé par le produit de la famille d'ensembles (graphe fonctionnel)."""
    return cardinal(E.produit_famille(f, i))


# @livre Ch.III §3.5 Def.4 | E III.28 L.20-21 | PDF p.131
# @livre Ch.III §3.5 Rem.- | E III.28 L.23-27 | PDF p.131
#   (petit texte « L'abus provient de ce que cette notation désigne déjà l'ensemble
#    des graphes fonctionnels … » ; prose sur la notation a^b, rien à formaliser.)
def exposant_cardinal(a, b):
    """a^b := Card(a^b) = Card({f | f : b → a})   (exponentiation, E.III.3.5, Déf. 4).

    Cardinal de l'ensemble des applications de b dans a (terme exposant(b, a))."""
    return cardinal(E.exposant(b, a))


__all__ = ["est_bijection_de", "equipotent", "cardinal", "CARD_VIDE", "est_cardinal",
           "est_injection_de", "inf_egal_card", "inf_strict_card",
           "relation_ordre_cardinaux", "somme_cardinale", "produit_cardinal",
           "exposant_cardinal"]
