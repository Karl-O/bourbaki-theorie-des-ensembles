"""Résumé §2 n°3 — FONCTION CONSTANTE  (E.R.6, « fonction constante dans E »).

Bourbaki (Résumé, E.R.6, §2, n°3) :
  « Une fonction définie dans un ensemble E, et prenant une même valeur a pour
    tout élément x de E, est dite constante dans E ; elle est déterminée par la
    relation fonctionnelle y = a. »

La fonction constante de E dans C de valeur a est donc la fonction x↦a (x∈E),
c'est-à-dire la fonction-terme `fonction_terme(E, a, C)` dont le TERME est le
terme CONSTANT a (a ne contient pas x libre).  Son graphe est
    F := graphe_terme(E, a) = {(x, a) | x ∈ E}
(spécialisation T := a, x non libre dans a, du graphe x↦T de C54, E.II.46).

On certifie ici, par SPÉCIALISATION (T := a) des théorèmes déjà certifiés du
graphe-terme — donc RIEN de neuf au niveau du noyau, juste l'instance T = a :

  • `graphe_constante_fonctionnel`  ⊢ F est fonctionnel   (CLOS, 0 hypothèse).
        C'est le contenu vérifiable de « y = a est une relation FONCTIONNELLE »
        (n°3) : la relation y = a détermine bien UNE fonction.  Instance de
        `ensembles_fonction_terme.graphe_terme_fonctionnel` avec t := a.

  • `valeur_constante`  {u ∈ E} ⊢ F(u) = a   (hypothèse u∈E, fidèle à
        « pour tout élément x de E »).  C'est « prenant une même valeur a » :
        la fonction vaut a en CHAQUE point u de E.  Instance de
        `ensembles_cantor.graphe_terme_valeur` avec t := a.

DÉPENDANCE / pureté.  Comme son patron `graphe_terme_fonctionnel`, le théorème
fonctionnel s'appuie sur la THÉORIE DÉDIÉE `theorie_graphe_terme(E, a)` — la
définition C54 du graphe (existence par S8, unicité par A1, exactement comme
produit/réciproque/restriction).  Cet axiome de DÉFINITION est l'instance T = a
de celui dont hérite le voisin ; il N'AJOUTE PAS d'axiome à `theorie_ensembles`
(qui reste à 22).  La fonctionnalité elle-même repose sur l'unicité A1, déjà
certifiée dans `graphe_terme_fonctionnel`.  On en hérite légitimement et on le
documente, comme le voisin — rien n'est caché.

PRÉCONDITION DE FIDÉLITÉ.  « a constant » = x non libre dans a (`x ∉ libres_t(a)`).
La fonction `fonction_constante` la VÉRIFIE (assertion) : si x figurait librement
dans a, ce ne serait plus la fonction constante de Bourbaki mais la fonction
x↦a(x).  Le noyau reste correct dans les deux cas ; l'assertion garantit la
FIDÉLITÉ au n°3 (a est bien une valeur fixe, indépendante de x).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, libres_t
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_6_fonction_terme.ensembles_fonction_terme import graphe_terme_fonctionnel
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_valeur


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.R §2.3 Def.3 | E.R.6 L.34-36 | PDF p.309
def fonction_constante(e="E", a="a", c="C", x="x"):
    """La fonction CONSTANTE x↦a de E dans C  (Résumé §2 n°3, E.R.6).

    Renvoie l'assemblage `fonction_terme(E, a, C)` = ((graphe_terme(E,a), E), C),
    la fonction-terme de E dans C dont le terme est le terme CONSTANT a.

    Précondition de fidélité : x ne figure pas librement dans a (sinon a n'est
    pas une valeur fixe et la fonction ne serait pas « constante » au sens du
    n°3).  Vérifiée par assertion (le noyau reste correct sans elle ; l'assertion
    garde la FIDÉLITÉ à Bourbaki)."""
    vE, va, vC = _t(e), _t(a), _t(c)
    assert x not in libres_t(va), (
        "fonction_constante : la valeur a doit être CONSTANTE "
        f"(x='{x}' ne doit pas y figurer librement) — n°3, E.R.6.")
    return E.fonction_terme(vE, va, vC, x)


# @livre Ch.R §2.3 Prop.3 | E.R.6 L.36-36 | PDF p.309
def graphe_constante_fonctionnel(e="E", a="a", x="x", y="y"):
    """⊢ le graphe de la fonction constante x↦a est FONCTIONNEL.

    Forme : ⊢ (∀u)(∀v)(∀z)(((u,v)∈F et (u,z)∈F) ⇒ v=z),  F = graphe_terme(E,a).
    C'est « la relation y = a est fonctionnelle » (n°3) : a étant constant, la
    relation y = a détermine une fonction.  CLOS (0 hypothèse).

    Spécialisation T := a de `ensembles_fonction_terme.graphe_terme_fonctionnel`
    (cœur de C54) : hérite de la théorie dédiée `theorie_graphe_terme(E, a)`
    (déf. S8 + unicité A1) — `theorie_ensembles` reste à 22 axiomes."""
    va = _t(a)
    assert x not in libres_t(va), (
        "graphe_constante_fonctionnel : a doit être constant (x non libre).")
    return graphe_terme_fonctionnel(_t(e), va, x, y)


# @livre Ch.R §2.3 Prop.3 | E.R.6 L.34-35 | PDF p.309
def valeur_constante(e="E", a="a", u="u", x="x", y="y"):
    """{u ∈ E} ⊢ F(u) = a,   F = graphe_terme(E,a).

    « prenant une même valeur a pour tout élément x de E » (n°3) : en chaque
    point u de E la fonction constante vaut a.  Hypothèse u∈E (fidèle à « pour
    tout x de E »).

    Spécialisation T := a de `ensembles_cantor.graphe_terme_valeur` : comme T = a
    est constant, T[u] = (u|x)a = a, donc la valeur en u est a.  Hérite, via ce
    lemme, de la théorie dédiée du graphe-terme et de C46 (valeur)."""
    va = _t(a)
    assert x not in libres_t(va), (
        "valeur_constante : a doit être constant (x non libre).")
    return graphe_terme_valeur(_t(e), va, u, x, y)


__all__ = ["fonction_constante", "graphe_constante_fonctionnel", "valeur_constante"]
