"""§III.2.1 — Lemme 1 : ordre sur une réunion FILTRANTE d'ensembles ordonnés (E III.17).

Le lemme qui fonde la démonstration de la Prop. 3 (E III.16) : si (X_α) est une
famille d'ensembles ordonnés FILTRANTE pour ⊂ (tout couple est contenu dans un
troisième), les ordres se recollant deux à deux, alors il existe sur E = ⋃X_α
UN ORDRE ET UN SEUL induisant sur chaque X_α l'ordre donné — et sa démonstration
montre que le graphe de cet ordre est NÉCESSAIREMENT G = ⋃G_α.

STATUT : ÉNONCÉ FORMALISÉ (constructeurs ci-dessous sur les briques RÉELLES du
dépôt), DÉRIVATION NON FAITE (PARTIEL ; chantier listé dans CAMPAGNE_TROUS).
La propriété « filtrante pour ⊂ » est LITTÉRALEMENT le prédicat famille_dirigee
déjà déposé (recollement §III.3) ; la réunion ⋃ est union_famille (C60) ; la
cohérence des ordres et l'identité-pivot s'écrivent au niveau graphes avec
l'algèbre du chap. II.  Rien n'est postulé, aucun `Theoreme` n'est forgé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal)
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
    famille_dirigee)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §2.1 Rem.- | E III.17 L.1-1 | PDF p.120  (transition : la 1ʳᵉ assertion de la Prop.3 résulte du lemme)
# @livre Ch.III §2.1 Lem.1 | E III.17 L.2-7 | PDF p.120
#   (ordre unique sur la réunion d'une famille filtrante d'ensembles ordonnés ;
#    démo L.8-18 [graphe nécessairement ⋃G_α, cohérence deux à deux] et suite de
#    la démo de la Prop.3 L.19-32 [X_ι segments, E bien ordonné] : NON dérivées)
def hypothese_famille_filtrante(D, p: str = "pdir", q: str = "qdir",
                                r: str = "rdir") -> Terme:
    """« (X_α) filtrante pour ⊂ » (E III.17 L.2-4) — c'est MOT POUR MOT le
    prédicat famille_dirigee du dépôt : (∀p)(∀q)((p∈𝔇 et q∈𝔇) ⇒
    (∃r)(r∈𝔇 et p⊂r et q⊂r))."""
    return famille_dirigee(_t(D), p, q, r)


def hypothese_ordres_coherents(G_beta, G_alpha, X_alpha) -> Terme:
    """« l'ordre induit sur X_α par celui de X_β est l'ordre donné » (E III.17
    L.4-5), au niveau graphes (comme dans la démo L.15) :
        G_β ∩ (X_α × X_α) = G_α."""
    tXa = _t(X_alpha)
    return egal(E.intersection(_t(G_beta), E.produit(tXa, tXa)), _t(G_alpha))


def enonce_lemme1_graphe(G, D_graphes) -> Terme:
    """L'identité-PIVOT de la démonstration (E III.17 L.13-14) : le graphe de
    l'unique ordre cherché sur E = ⋃X_α est nécessairement

        G = ⋃_{α} G_α

    (𝔇 = la famille des graphes G_α ; ⋃ = union_famille du C60)."""
    return egal(_t(G), union_famille(_t(D_graphes)))


__all__ = ["hypothese_famille_filtrante", "hypothese_ordres_coherents",
           "enonce_lemme1_graphe"]
