"""§III.6.3 — Théorème 2 (HESSENBERG) : le RECOLLEMENT d'une CHAÎNE de bijections
est une BIJECTION (le majorant-recollement de l'argument de Zorn, E.III.48).

But : décharger (partiellement) le résidu `enonce_chaine_majoree` de
`ensembles_hessenberg_inductivite` en montrant que, pour une chaîne 𝔗 de couples
(S_i,φ_i) du poset 𝔉 (φ_i:S_i×S_i→S_i bijective, emboîtés par l'ordre de chaîne),
le couple-recollement (⋃S, ⋃φ) EST une frame-pair : ⋃φ est une BIJECTION de
(⋃S)×(⋃S) sur ⋃S.

────────────────────────────────────────────────────────────────────────────────
CE QUI EST GENUINEMENT CLOS ICI (réutilisation de l'infra FAMILLE déjà mergée) :

  (1) FONCTIONNALITÉ de ⋃φ — `union_chaine_fonctionnelle` (C60), sous l'hyp
      HONNÊTE famille_compatible(𝔇).  [déjà clos en amont, ré-exporté]

  (2) INJECTIVITÉ (au niveau des COUPLES, `injectif_graphe`) de ⋃φ —
      `union_chaine_injective`, instanciation DIRECTE de `union_famille_injective`
      (recollement-injectif FAMILLE) à la famille des φ-graphes.  Une CHAÎNE est
      DIRIGÉE (le plus petit s'emboîte dans le plus grand → famille_dirigee) et
      chaque φ_i est injective (membres_injectifs) → ⋃φ injective.  Les deux hyps
      famille_dirigee(𝔇)/membres_injectifs(𝔇) sont HONNÊTES.  CLOS via la famille,
      qui contourne le mur de capture de la variable de valeur en travaillant
      DIRECTEMENT sur les couples.

  (3) ASSEMBLAGE `union_chaine_bijection_graphe` : la CONJONCTION
        est_fonctionnel(⋃φ) ET injectif_graphe(⋃φ)
      sous les hyps HONNÊTES { famille_compatible(𝔇), famille_dirigee(𝔇),
      membres_injectifs(𝔇) }.  C'est le « graphe-niveau » de la bijection : les
      deux moitiés DURES (fonctionnalité + injectivité, déjà au niveau couple) du
      recollement de chaîne, réunies.  CLOS.

────────────────────────────────────────────────────────────────────────────────
OBSTRUCTIONS HONNÊTES (NON closes — transportées en antécédent, JAMAIS postulées) :

  • SURJECTIVITÉ de ⋃φ sur ⋃S (est_surjective, image(⋃φ,(⋃S)×(⋃S))=⋃S) : exige
    l'infra RECOLLEMENT-SURJECTIF version chaîne (chaque w∈⋃S est dans un S_i=img φ_i,
    donc atteint) — le dépôt n'a PAS cette infra famille.  Reste hyp honnête.

  • dom(⋃φ)=(⋃S)×(⋃S) : pareil, recollement-domaine version chaîne absent.

  • PONT couple→valeur : `injectif_graphe` (couple-natif, clos ici) vs
    `injective_dans` (valeur-gardée, requis par est_bijective) — le mur de la
    variable de valeur.  Le passage de l'un à l'autre n'est PAS fait.

  • FRAME-MEMBERSHIP (⋃S,⋃φ)∈𝔉(E) via l'axiome OPAQUE `axiome_frame` : exige de
    fournir le corps (∃S φ)(...) avec S:=⋃S, φ:=⋃φ — donc la bijection COMPLÈTE
    (les 4 obstructions ci-dessus).  NON assemblé.

  • `enonce_chaine_majoree` reste donc le résidu honnête de `frame_inductif` ; il
    n'est PAS déchargé inconditionnellement.  Ce module ferme les DEUX moitiés
    DURES couple-niveau (fonctionnalité + injectivité) du recollement de chaîne ;
    voir RAPPORT pour l'obstruction exacte.

INVARIANT : theorie_ensembles() reste = 22.  Aucun axiome nouveau ; rien postulé ;
ni la bijection complète ni l'inductivité ne sont supposées vraies (antécédent).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, famille_compatible,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
    injectif_graphe, famille_dirigee, membres_injectifs,
    union_famille_injective,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_inductivite import (
    union_chaine_fonctionnelle,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (2) INJECTIVITÉ du recollement d'une CHAÎNE de bijections (niveau COUPLE).
#      Instanciation DIRECTE de `union_famille_injective` : une chaîne est dirigée.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.23-24 | PDF p.151  (« on vérifie aussitôt que 𝔐 est un ensemble inductif » : injectivité du recollement de chaîne)
def union_chaine_injective(D="Dchaine"):
    """{ famille_dirigee(𝔇), membres_injectifs(𝔇) } ⊢ injectif_graphe( ⋃𝔇 ).
                                                              [2 hyps HONNÊTES].

    🎯 INJECTIVITÉ du recollement de chaîne (l'autre moitié dure, à côté de la
    fonctionnalité).  Pour une CHAÎNE de φ-graphes injectifs à domaines emboîtés,
    la réunion ⋃φ est injective : c'est `union_famille_injective` appliqué tel quel,
    une chaîne étant DIRIGÉE (famille_dirigee : le plus petit s'emboîte dans le plus
    grand, lequel sert de r).  Travaille au niveau des COUPLES (`injectif_graphe`),
    ce qui contourne le mur de capture de la variable de valeur.  Les 2 hyps sont
    HONNÊTES (jamais postulées vraies ; conclusion ∉ hyps ; theorie=22)."""
    return union_famille_injective(D)


# ════════════════════════════════════════════════════════════════════════════
#  (3) ASSEMBLAGE — les DEUX moitiés DURES (fonctionnalité ET injectivité) du
#      recollement de chaîne, réunies au niveau du GRAPHE ⋃φ.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.23-24 | PDF p.151  (recollement de chaîne : fonctionnalité + injectivité au niveau graphe)
def union_chaine_bijection_graphe(D="Dchaine"):
    """{ famille_compatible(𝔇), famille_dirigee(𝔇), membres_injectifs(𝔇) }
         ⊢ ( est_fonctionnel(⋃𝔇) et injectif_graphe(⋃𝔇) ).
                                                        [3 hyps HONNÊTES, CLOS].

    🎯 Le « graphe-niveau » de la bijection-recollement de chaîne : la CONJONCTION
    des deux moitiés DURES déjà closes —
        • FONCTIONNALITÉ via `union_chaine_fonctionnelle` (C60),
        • INJECTIVITÉ (couple) via `union_chaine_injective` (= union_famille_injective).
    Sous les 3 hypothèses HONNÊTES famille_compatible / famille_dirigee /
    membres_injectifs (jamais postulées vraies ; conclusion ∉ hyps ; theorie=22).

    Manquent encore, pour la bijection COMPLÈTE est_bijection_de (donc pour la
    frame-membership (⋃S,⋃φ)∈𝔉 et le majorant) : SURJECTIVITÉ sur ⋃S, dom=(⋃S)×(⋃S),
    et le pont couple→valeur (injectif_graphe→injective_dans).  Ce sont les
    obstructions honnêtes, voir docstring de module + RAPPORT."""
    vD = _t(D)
    th_fonc = union_chaine_fonctionnelle(vD)              # est_fonctionnel(⋃𝔇)  [famille_compatible]
    th_inj = union_chaine_injective(vD)                   # injectif_graphe(⋃𝔇)  [famille_dirigee, membres_injectifs]
    res = conjonction_intro(th_fonc, th_inj)
    U = union_famille(vD)
    cible = et(E.est_fonctionnel(U), injectif_graphe(U))
    assert res.conclusion == cible, "union_chaine_bijection_graphe : ≠ (fonctionnel et injectif)"
    assert famille_compatible(vD) in res.hypotheses, "manque famille_compatible"
    assert famille_dirigee(vD) in res.hypotheses, "manque famille_dirigee"
    assert membres_injectifs(vD) in res.hypotheses, "manque membres_injectifs"
    assert res.conclusion not in res.hypotheses, "union_chaine_bijection_graphe : VACUOUS"
    return res


__all__ = [
    "union_chaine_injective",
    "union_chaine_bijection_graphe",
]
