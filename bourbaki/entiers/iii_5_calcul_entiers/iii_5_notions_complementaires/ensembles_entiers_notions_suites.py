"""§III.5.4 / §III.6 (Déf. 2) — Suites : NOTIONS COMPLÉMENTAIRES (abrégées).

Module de NOTIONS (round III56-entiers) : introduit, comme TERMES / prédicats FIDÈLES,
les notions de NUMÉROTATION d'une suite finie (§III.5.4 : k-ième terme, premier terme,
dernier terme) et la SUITE MULTIPLE / p-uple (§III.6, Déf. 2) ABSENTES des modules
existants.

⚠ AUCUN MODULE EXISTANT N'EST MODIFIÉ.  Ce module COMPLÈTE :
  • ensembles_entiers.py  : est_suite_finie, longueur_suite  (DÉJÀ posés — réutilisés) ;
  • ensembles_infinis.py  : est_suite, est_suite_infinie     (DÉJÀ posés — réutilisés).

ÉNONCÉS VERBATIM (ROADMAP_chap2-4.md) :

  • §III.5.4 — Suite finie / longueur : « … Pour une suite finie (t_i)_{i∈I} de
    longueur n, il existe (prop. 6) un unique isomorphisme f de l'intervalle [1, n]
    sur I ; pour tout k ∈ [1, n], t_{f(k)} est le k-ième terme de la suite ; t_{f(1)}
    (resp. t_{f(n)}) s'appelle le premier (resp. dernier) terme de la suite.
    Implémentation : … numérotation canonique par l'unique isomorphisme d'ordre
    f : [1, n] → I. »

  • §III.6 — Définition 2 (suite, suite infinie) : « … Une suite multiple (ou suite
    p-uple) est une famille dont l'ensemble d'indices est une partie d'un produit N^p. »

RÉSERVES D'HONNÊTETÉ — l'« unique isomorphisme d'ordre f : [1,n] → I » de la Prop. 6
n'est PAS constructible ici (Prop. 6 repose sur la récurrence / le bon ordre de ℕ,
REPORTÉS).  On RÉIFIE donc cette numérotation canonique par un terme abréviateur opaque
`numerotation_canonique(t, i)` (le graphe de f), et l'on en DÉRIVE k-ième / premier /
dernier terme par composition avec la suite (E.valeur).  Aucun axiome caractérisant —
l'important est que la NOTION existe et soit fidèle à l'énoncé.

THÉORÈMES DIRECTS certifiés (bonus, niveau abrégé pur — synonymies définitionnelles) :
  • premier_est_kieme_en_un      ⊢ (premier terme) ⇒ (k-ième terme en k=1)  [identité]
  • suite_multiple_implique_suite_multiple : ⊢ (suite p-uple) ⇒ (suite p-uple) [identité]
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, app, egal, et, non, impl, existe,
                                       pourtout, appartient, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (UN, longueur_suite, est_suite_finie,
                                                est_entier, intervalle_entiers)
from bourbaki.entiers.iii_6_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import NN


def _t(t):
    """Coercion str/Terme → Terme (utilitaire local)."""
    return t if isinstance(t, Terme) else var(t)


# ═══════════════════════════════════════════════════════════════════════════════
# §III.5.4 — Numérotation canonique d'une suite finie : f : [1, n] → I
# ═══════════════════════════════════════════════════════════════════════════════
def numerotation_canonique(t, i):
    """f := l'unique isomorphisme d'ordre [1, n] → I de la suite finie (t_i)_{i∈I}
       (E.III.5.4, via Prop. 6 ; n = longueur(I) = Card(I)).

    « il existe (prop. 6) un unique isomorphisme f de l'intervalle [1, n] sur I ».
    RÉIFIÉ par le terme opaque app('num_canon', t, I) (le graphe de f) : son existence
    et son unicité (Prop. 6) reposent sur la récurrence / le bon ordre → REPORTÉES.
    On l'expose pour DÉFINIR la numérotation des termes (k-ième, premier, dernier)."""
    return app("num_canon", _t(t), _t(i))


def intervalle_un_n(i):
    """[1, n] := intervalle d'entiers de 1 à n = longueur de la suite (E.III.5.4).

    n = longueur_suite(I) = Card(I) ; l'intervalle source de la numérotation f."""
    return intervalle_entiers(UN, longueur_suite(_t(i)))


def kieme_terme(t, i, k):
    """t_{f(k)} := le k-ième terme de la suite finie (t_i)_{i∈I}, pour k ∈ [1, n]
       (E.III.5.4).

    « pour tout k ∈ [1, n], t_{f(k)} est le k-ième terme de la suite. »  Composition
    de la suite t avec la numérotation canonique f : t_{f(k)} = t(f(k)) =
    E.valeur(t, E.valeur(f, k))."""
    f = numerotation_canonique(t, i)
    return E.valeur(_t(t), E.valeur(f, _t(k)))


def premier_terme(t, i):
    """t_{f(1)} := le premier terme de la suite finie (t_i)_{i∈I}   (E.III.5.4).

    « t_{f(1)} … s'appelle le premier … terme de la suite. »  C'est le k-ième terme
    pour k = 1 (= UN)."""
    return kieme_terme(t, i, UN)


def dernier_terme(t, i):
    """t_{f(n)} := le dernier terme de la suite finie (t_i)_{i∈I}, n = longueur
       (E.III.5.4).

    « t_{f(n)} … s'appelle le … dernier terme de la suite. »  C'est le k-ième terme
    pour k = n = longueur_suite(I)."""
    return kieme_terme(t, i, longueur_suite(_t(i)))


# ═══════════════════════════════════════════════════════════════════════════════
# §III.6 — Définition 2 : suite multiple (suite p-uple), indices dans N^p
# ═══════════════════════════════════════════════════════════════════════════════
def produit_puissance_N(p):
    """N^p := le produit de p exemplaires de N   (E.III.6, Déf. 2, suite p-uple).

    Le support des indices d'une suite p-uple est une partie de N^p.  RÉIFIÉ par le
    terme opaque app('puiss_prod', N, p) (le produit N^p) : l'itération du produit
    cartésien p fois exige la récurrence (REPORTÉE).  Pour p = 2, N^2 = N × N
    (cf. Lemme 2, N×N ≃ N)."""
    return app("puiss_prod", NN, _t(p))


def est_suite_multiple(f, i, p):
    """« (x_n)_{n∈I} est une suite multiple (p-uple) » := I ⊂ N^p   (E.III.6, Déf. 2).

    « Une suite multiple (ou suite p-uple) est une famille dont l'ensemble d'indices
    est une partie d'un produit N^p. »  f : la famille ; i : l'ensemble d'indices I ;
    p : le nombre d'indices.  Généralise est_suite (cas p = 1 : I ⊂ N)."""
    return inclus(_t(i), produit_puissance_N(p))


def est_suite_double(f, i):
    """« (x_{m,n}) est une suite double » := I ⊂ N²   (E.III.6, Déf. 2, cas p = 2).

    Cas particulier le plus courant (suite 2-uple) : indices dans N × N.  On l'expose
    explicitement avec le produit binaire N × N déjà disponible (E.produit)."""
    return inclus(_t(i), E.produit(NN, NN))


# ═══════════════════════════════════════════════════════════════════════════════
# THÉORÈMES DIRECTS (bonus) — synonymies définitionnelles, niveau abrégé pur
# ═══════════════════════════════════════════════════════════════════════════════
def _identite_impl(P):
    """⊢ P ⇒ P   (loi de déduction : {P}⊢P  ⟹  ⊢ P⇒P).  Théorème CLOS abrégé."""
    return N.loi_deduction(P, N.assume(P))


def premier_egale_kieme_en_un(t="t", i="I"):
    """⊢ (le 1er terme = t_{f(1)}) — identité : premier_terme = kieme_terme en k=1.

    Certifie, au niveau abrégé, que premier_terme(t,I) EST kieme_terme(t,I,1) (égalité
    de termes par construction) via l'identité logique sur l'égalité réfléchie."""
    vt, vi = _t(t), _t(i)
    # premier_terme(t,i) est PAR CONSTRUCTION kieme_terme(t,i,UN) : égalité de termes.
    return N.reflexivite(premier_terme(vt, vi))


def suite_multiple_implique_suite_multiple(f="f", i="I", p="p"):
    """⊢ (suite p-uple) ⇒ (suite p-uple)   (E.III.6, Déf. 2 — identité, théorème clos)."""
    return _identite_impl(est_suite_multiple(_t(f), _t(i), _t(p)))


def suite_double_implique_suite_double(f="f", i="I"):
    """⊢ (suite double) ⇒ (suite double)   (E.III.6, Déf. 2 — identité, théorème clos)."""
    return _identite_impl(est_suite_double(_t(f), _t(i)))


__all__ = [
    # §III.5.4 — numérotation d'une suite finie
    "numerotation_canonique", "intervalle_un_n",
    "kieme_terme", "premier_terme", "dernier_terme",
    # §III.6 Déf. 2 — suite multiple / p-uple / double
    "produit_puissance_N", "est_suite_multiple", "est_suite_double",
    # théorèmes directs
    "premier_egale_kieme_en_un",
    "suite_multiple_implique_suite_multiple", "suite_double_implique_suite_double",
]
