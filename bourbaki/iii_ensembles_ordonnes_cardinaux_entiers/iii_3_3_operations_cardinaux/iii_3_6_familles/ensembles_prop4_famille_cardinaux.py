"""§III.3.3 Prop.4 (n°101) — Card(∏E_ι)=∏Card(E_ι) et Card(∑E_ι)=∑Card(E_ι).

Bourbaki (E III.26, Prop.4) : soient (E_ι)_{ι∈I} une famille d'ensembles, P son
produit, S sa somme, a_ι = Card(E_ι) ; alors Card(P) = ∏_ι a_ι et Card(S) = ∑_ι a_ι.

Rappel des définitions (ensembles_cardinaux.py, Déf. 3, DÉJÀ formalisées) :
  ∏_ι a_ι := produit_cardinal(A, I) := Card(produit_famille(A, I))
  ∑_ι a_ι := somme_cardinale(A, I)  := Card(somme_famille(A, I))
où A = (a_ι)_{ι∈I} = (Card E_ι)_{ι∈I} est la FAMILLE DES CARDINAUX.

Donc Prop.4 s'écrit :
  Card(produit_famille(E, I)) = Card(produit_famille(A, I))   (produit)
  Card(somme_famille(E, I))   = Card(somme_famille(A, I))     (somme)
i.e. il s'agit d'ÉQUIPOTENCES  produit_famille(E) ≅ produit_famille(A)  et
somme_famille(E) ≅ somme_famille(A), induites, coordonnée par coordonnée, par les
bijections canoniques  E_ι ≅ Card(E_ι)  (equipotent_son_cardinal).

DÉCOMPOSITION EN BRIQUES (sous-campagne multi-tick, façon n°111) :
  · BRIQUE 1 (CE fichier) — la FAMILLE DES CARDINAUX A = ι↦Card(E_ι), construite par
    graphe_terme (C54).  ⚠️ Sa caractérisation de valeur (A(ι)=Card E_ι via
    graphe_terme_valeur) est BLOQUÉE par le VERROU-τ : le terme-valeur Card(E_ι) est un
    τ binder-riche {F,Z,u,up,v,y,z} qui collisionne les liants internes de
    graphe_terme_valeur (échec « modus ponens : mineure ≠ antécédent », même y frais).
    Levée = contournement par index (liants FRAIS) = SESSION DÉDIÉE.  Cf. carte_cardinaux_valeur.
  · BRIQUE 2 (à venir) — la FAMILLE DE BIJECTIONS B = ι↦τ-bij(E_ι, Card E_ι) via
    graphe_terme, avec {ι∈I} ⊢ est_bijection_de(B(ι), E_ι, Card E_ι)
    [equipotent_son_cardinal + existe_temoin].
  · BRIQUE 3 (à venir, LE gros morceau) — FONCTORIALITÉ du produit de famille :
    « une famille (b_ι) de bijections X_ι→Y_ι induit une bijection ∏X_ι→∏Y_ι »
    (image_produit via produit_props_fonctoriel : coord_image_produit,
    membre_produit_famille, extensionnalite_produit).  L'analogue BINAIRE existe
    (produit_est_bijection) ; ici il faut la version FAMILLE indexée.
  · BRIQUE 4 — idem pour la SOMME (recollement INDEXÉ, absent : cf. note
    ensembles_recollement_props.py L.63 « exige un recollement INDEXÉ »).
  · ASSEMBLAGE — Prop.4 produit (B3 sur B=bij canoniques) puis somme (B4).

theorie_ensembles() inchangée (22 axiomes).  Rien postulé.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, Terme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, produit_cardinal, somme_cardinale)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _famille_cardinaux(e, i, iota="iota"):
    """A := (Card E_ι)_{ι∈I} = graphe_terme(I, Card(E_ι), ι)   (famille des cardinaux).

    E est la famille (E_ι) (fonction) ; E_ι = valeur_famille(E, ι) ; le terme-valeur
    est Card(E_ι), de variable libre ι.  A est un graphe fonctionnel de domaine I."""
    vi = _t(i)
    T = cardinal(E.valeur_famille(_t(e), var(iota)))     # terme-valeur ι ↦ Card(E_ι)
    return E.graphe_terme(vi, T, iota)


def enonce_carte_cardinaux_valeur(e="E", i="I", i0="i0", iota="iota"):
    A = _famille_cardinaux(e, i, iota)
    vi0 = _t(i0)
    return egal(E.valeur(A, vi0), cardinal(E.valeur_famille(_t(e), vi0)))


# @livre Ch.III §3.3 Meta.- | E III.26 L.1-4 | PDF p.129  (caractérisation de valeur de la famille des cardinaux — DÉBLOQUÉE par le fix subst)
def carte_cardinaux_valeur(e="E", i="I", i0="i0", iota="iota"):
    """{ ι₀∈I } ⊢ A(ι₀) = Card(E_{ι₀})                              [1 hyp honnête].

    ✅ DÉBLOQUÉ (25 juil 2026) : l'ancien « verrou-τ » (collision des liants
    {F,Z,u,up,v,y,z} du τ-cardinal avec ceux de graphe_terme_valeur, « modus ponens :
    mineure ≠ antécédent ») était un RENOMMAGE GRATUIT de la substitution, supprimé
    par le court-circuit CS de subst_t/subst_f — `graphe_terme_valeur` construit
    désormais directement sur le terme-valeur Card-valué (sondé et vert).  La voie
    vers Prop.4 (fonctorialité indexée B2-B4) est ouverte côté valuation."""
    ve, vi = _t(e), _t(i)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import graphe_terme_valeur
    T = cardinal(E.valeur_famille(ve, var(iota)))        # ι ↦ Card(E_ι)
    # graphe_terme_valeur attend des NOMS (var(u)) — i0 doit être un nom ; pour un
    # TERME, ∀-clore ce théorème sur i0 puis instancie (motif _inst_gen).
    res = graphe_terme_valeur(vi, T, i0, iota)           # {i0∈I} ⊢ A(i0)=T[i0]
    cible = enonce_carte_cardinaux_valeur(e, i, i0, iota)
    assert res.conclusion == cible, "carte_cardinaux_valeur : ≠ A(i0)=Card(E_i0)"
    assert len(res.hypotheses) == 1, "carte_cardinaux_valeur : hyps ≠ 1"
    return res


def enonce_prop4_produit(e="E", i="I", iota="iota"):
    """Card(produit_famille(E, I)) = ∏_ι Card(E_ι)   (Prop.4, moitié produit)."""
    ve, vi = _t(e), _t(i)
    A = _famille_cardinaux(e, i, iota)
    return egal(cardinal(E.produit_famille(ve, vi)), produit_cardinal(A, vi))


def enonce_prop4_somme(e="E", i="I", iota="iota"):
    """Card(somme_famille(E, I)) = ∑_ι Card(E_ι)   (Prop.4, moitié somme)."""
    ve, vi = _t(e), _t(i)
    A = _famille_cardinaux(e, i, iota)
    return egal(cardinal(E.somme_famille(ve, vi)), somme_cardinale(A, vi))


__all__ = ["_famille_cardinaux", "enonce_carte_cardinaux_valeur", "carte_cardinaux_valeur",
           "enonce_prop4_produit", "enonce_prop4_somme"]
