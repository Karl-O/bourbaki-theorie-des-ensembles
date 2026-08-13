"""§III.2.1 — Un ensemble bien ordonné est TOTALEMENT ordonné.

    ⊢ est_bien_ordonne(R,E)  ⇒  est_totalement_ordonne(R,E).

où (E.III.1.12, Déf. 9)

    est_totalement_ordonne(R,E) = ( est_relation_ordre_dans(R,E)
                                    et (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ou R{y,x})) ).

PREUVE (E.III.2.1).  La Définition 1 du bon ordre est une conjonction « E ordonné
par R  et  toute partie non vide a un plus petit élément ».  On en tire les DEUX
composantes de l'ordre total :

  (gauche)  est_relation_ordre_dans(R,E)  par PROJECTION GAUCHE de la définition du
            bon ordre (brique `bien_ordonne_est_ordonne`, §III.2.1).
  (droite)  la TOTALITÉ (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ou R{y,x})) par la brique
            `bon_ordre_est_total` (§III.2 trichotomie) : on applique la clause de
            plus petit élément à la paire {x,y}.

`conjonction_intro` des deux recolle EXACTEMENT le prédicat est_totalement_ordonne.

⚠ COHÉRENCE DES BINDERS DE R.  R est porté comme GRAPHE (R-as-function bourbakien) :
Rf = λa,b. (a,b)∈R, identique à `bon_ordre_est_total`.  Les deux briques portent alors
la MÊME hypothèse est_bien_ordonne(Rf,E) canonique, qui FUSIONNE en une seule (pas de
variante redondante).  Vérifié par == dans le test : conclusion == est_totalement_ordonne(Rf,E)
et hypotheses == {est_bien_ordonne(Rf,E)} (un seul élément).

INVARIANT : theorie_ensembles() = 22.  Rien postulé (tout dérivé du bon ordre) ; non
vacueux (le bon ordre est réellement consommé, l'unique hypothèse est est_bien_ordonne).

Pièce order-théorique PURE : aucun import lourd au chargement, construction <1 ms.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, appartient
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.bon_ordre_segments.ensembles_bon_ordre import (
    bien_ordonne_est_ordonne,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_bien_ordonne_total import (
    bon_ordre_est_total,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _R_de(R):
    """Relation (a,b)↦(a,b)∈R associée au graphe R (R-as-function bourbakien).

    STRICTEMENT aligné sur `ensembles_bien_ordonne_total._R_de` pour que l'hypothèse
    est_bien_ordonne(Rf,E) de `bon_ordre_est_total` FUSIONNE avec celle de la
    projection gauche (mêmes binders, même forme de graphe)."""
    vR = _t(R)
    return lambda a, b: appartient(E.couple(_t(a), _t(b)), vR)


# ════════════════════════════════════════════════════════════════════════════
#  🎯 Un bon ordre est total.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.1 Rem.- | E III.15 L.33-35 | PDF p.118
def bien_ordonne_est_total(R="R", E_set="E", x="x", y="y"):
    """⊢ { est_bien_ordonne(R,E) } ⊢ est_totalement_ordonne(R,E).

    SÉQUENT à UNE hypothèse (est_bien_ordonne(Rf,E)), conclusion exactement
    est_totalement_ordonne(Rf,E).  Forme close : `bien_ordonne_est_total_clos`."""
    Rf = _R_de(R)
    ve = _t(E_set)

    hyp = E.est_bien_ordonne(Rf, ve)             # est_bien_ordonne(R,E) CANONIQUE
    Hbo = N.assume(hyp)

    # (gauche)  est_relation_ordre_dans(R,E)  — projection gauche du bon ordre.
    imp_ord = bien_ordonne_est_ordonne(Rf, E_set)   # ⊢ bo ⇒ est_relation_ordre_dans(R,E)
    ord_dans = N.modus_ponens(Hbo, imp_ord)         # est_relation_ordre_dans(R,E)  [hyp]

    # (droite)  totalité (∀x)(∀y)((x∈E et y∈E) ⇒ (R{x,y} ou R{y,x})).
    tot = bon_ordre_est_total(R, E_set, x, y)       # clause de totalité  [hyp]

    # recollage : est_totalement_ordonne(R,E) = (ord_dans et totalité).
    return conjonction_intro(ord_dans, tot)         # est_totalement_ordonne(R,E)  [hyp]


def bien_ordonne_est_total_clos(R="R", E_set="E", x="x", y="y"):
    """⊢ est_bien_ordonne(R,E) ⇒ est_totalement_ordonne(R,E).

    Forme CLOSE (0 hypothèse) : la clause de bon ordre est déchargée par S3."""
    thm = bien_ordonne_est_total(R, E_set, x, y)
    bo = list(thm.hypotheses)[0]          # l'unique hypothèse = est_bien_ordonne(R,E)
    return N.loi_deduction(bo, thm)


def bien_ordonne_est_total_cible(R="R", E_set="E", x="x", y="y"):
    """ÉNONCÉ-cible (test miroir) de la conclusion de `bien_ordonne_est_total`."""
    Rf = _R_de(R)
    ve = _t(E_set)
    return E.est_totalement_ordonne(Rf, ve, x, y)


__all__ = [
    "bien_ordonne_est_total",
    "bien_ordonne_est_total_clos",
    "bien_ordonne_est_total_cible",
]
