"""§III.6.3 — Théorème 2 (HESSENBERG), INDUCTIVITÉ du poset 𝔉 de Zorn.

« THÉORÈME 2 (E.III.47, §III.6.3) : pour tout cardinal infini 𝔞, on a 𝔞² = 𝔞. »
(PDF source lu, p.E III.47 : « THÉORÈME 2. — Pour tout cardinal infini 𝔞, on a
𝔞² = 𝔞.  Nous utiliserons deux lemmes.  Lemme 1. — Tout ensemble infini E
contient un ensemble équipotent à N. »)

L'argument de Bourbaki (E.III.48) ordonne le poset 𝔉 des couples (S,φ),
φ:S×S→S bijective, par EXTENSION, et invoque :
    « On vérifie aussitôt que 𝔐 est INDUCTIF (réunion d'une chaîne : union des X,
      union des ψ — recollement de bijections à domaines emboîtés). »

Ce module attaque la PREMIÈRE des deux parties dures (l'autre étant
« maximal ⇒ Card(F)=𝔞 ») : l'INDUCTIVITÉ de 𝔉, i.e. toute chaîne 𝔗 de 𝔉
possède un majorant — à savoir le couple (⋃S, ⋃φ) obtenu par RECOLLEMENT.

────────────────────────────────────────────────────────────────────────────────
CŒUR ATTEIGNABLE et CLOS ICI — la FONCTIONNALITÉ du recollement de la chaîne :

  La réunion ⋃𝔇 d'une famille de graphes COMPATIBLE PAR PAIRES est un graphe
  FONCTIONNEL.  C'est l'ingrédient pivot de « union des ψ = bijection » : pour une
  CHAÎNE de bijections à domaines emboîtés, deux membres s'accordent sur tout
  antécédent commun (le plus petit s'étend dans le plus grand), donc la famille
  est compatible, donc ⋃φ est fonctionnel.  On RÉUTILISE l'infra FAMILLE de C60
  (`union_famille_fonctionnelle`, `valeur_union_famille`) — bâtie pour la
  récurrence transfinie, elle s'applique TELLE QUELLE au recollement de chaîne.

  `union_chaine_fonctionnelle`  { famille_compatible(𝔇) } ⊢ est_fonctionnel(⋃𝔇)
        — CLOS, 1 hyp honnête (la compatibilité de la chaîne), via C60.

────────────────────────────────────────────────────────────────────────────────
ÉTAT HONNÊTE (ce module).  Sont CLOS :

  • `union_chaine_fonctionnelle`  — la FONCTIONNALITÉ de ⋃φ (crux fonctionnel),
        sous l'hypothèse HONNÊTE famille_compatible(𝔇).  Réutilise C60.
  • `union_chaine_valeur`         — la COÏNCIDENCE de valeur ⋃φ(u)=φ_i(u) sur
        chaque morceau (transfert de valeur), sous hyps honnêtes.  Réutilise C60.
  • `frame_inductif`              — l'ÉNONCÉ d'inductivité est_inductif(Γ𝔉,𝔉),
        SOUS l'hypothèse HONNÊTE « toute chaîne admet un majorant dans 𝔉 »
        (l'existence du majorant-recollement), JAMAIS supposée vraie : elle est
        transportée en antécédent.  C'est l'échafaudage qui branche le
        recollement sur la définition `est_inductif` de §III.2.

RÉSIDU HONNÊTE (le SEUL verrou de l'inductivité, JAMAIS postulé vrai) :
  `enonce_chaine_majoree(Γ𝔉,𝔉)` :  toute chaîne 𝔗 de 𝔉 admet un majorant dans 𝔉,
le majorant étant (⋃S,⋃φ).  Sa preuve COMPLÈTE exige, OUTRE la fonctionnalité
(close ici), l'INJECTIVITÉ et la SURJECTIVITÉ de ⋃φ sur (⋃S)×(⋃S) — il manque
l'infra RECOLLEMENT-INJECTIF/SURJECTIF en version FAMILLE/chaîne (le dépôt n'a
que la version BINAIRE `reunion_graphes_injective`).  C'est l'obstruction exacte ;
voir RAPPORT.

INVARIANT : theorie_ensembles() reste = 22.  Rien n'est postulé ; ni a²=a ni
l'inductivité ne sont supposés vrais (toujours en antécédent).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, existe, pourtout, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, majorant, totalement_ordonne,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif, chaine
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, famille_compatible,
    union_famille_fonctionnelle, valeur_union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  (i) FONCTIONNALITÉ du recollement d'une CHAÎNE de bijections.
#      ⋃φ est fonctionnel dès que la famille des φ est compatible par paires.
#      RÉUTILISE l'infra FAMILLE de C60 (bâtie pour la récurrence transfinie).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.23-24 | PDF p.151  (fonctionnalité de ⋃ψ, pivot du recollement de chaîne)
def union_chaine_fonctionnelle(D="Dchaine"):
    """{ famille_compatible(𝔇) } ⊢ est_fonctionnel( ⋃𝔇 ).            [1 hyp honnête].

    🎯 LE CRUX FONCTIONNEL de « union des ψ = bijection » (E.III.48).  Pour une
    CHAÎNE de graphes-bijections à domaines emboîtés, deux membres s'accordent sur
    tout antécédent commun (le plus petit S-graphe s'étend dans le plus grand par
    l'ordre de chaîne), donc la famille est COMPATIBLE PAR PAIRES.  La réunion ⋃𝔇
    est alors un graphe FONCTIONNEL : c'est exactement `union_famille_fonctionnelle`
    de C60 (l'infra de la récurrence transfinie se réemploie telle quelle pour le
    recollement de chaîne de Zorn).  L'hypothèse famille_compatible(𝔇) est HONNÊTE
    (jamais postulée vraie ; conclusion ∉ hyps ; theorie=22)."""
    return union_famille_fonctionnelle(D)


# @livre Ch.III §6.3 Demo.2 | E III.48 L.23-24 | PDF p.151  (coïncidence de valeur ⋃ψ(u)=ψᵢ(u) sur chaque morceau)
def union_chaine_valeur(D="Dchaine", p="pcf", u="u"):
    """{ famille_compatible(𝔇), p∈𝔇, u∈dom(p) } ⊢ valeur(⋃𝔇,u)=valeur(p,u).

    🎯 COÏNCIDENCE de valeur du recollement de chaîne : sur le domaine de chaque
    membre p (= chaque morceau S_i×S_i de la chaîne), la réunion ⋃φ rend la même
    valeur que φ_i.  C'est `valeur_union_famille` de C60, réemployé tel quel pour
    la chaîne de bijections (E.III.48, « union des ψ »).  3 hyps HONNÊTES."""
    return valeur_union_famille(D, p, u)


# ════════════════════════════════════════════════════════════════════════════
#  (ii) RÉSIDU HONNÊTE — l'existence d'un majorant pour toute chaîne de 𝔉.
#       C'est l'unique verrou de l'inductivité (jamais postulé vrai).
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.23-24 | PDF p.151  (énoncé « toute chaîne de 𝔐 admet un majorant »)
def enonce_chaine_majoree(G, E_set, C="C", m="m", x="x", y="y", z="z"):
    """enonce_chaine_majoree(Γ𝔉,𝔉) := (∀C)( chaine(Γ𝔉,𝔉,C) ⇒ (∃m) majorant(Γ𝔉,C,m,𝔉) ).

    « Toute chaîne 𝔗 de 𝔉 admet un MAJORANT dans 𝔉 » : c'est, mot pour mot, la
    seconde clause de la Définition 3 §III.2 (`est_inductif`).  Le majorant est le
    couple-recollement (⋃S,⋃φ) (E.III.48).  C'est le RÉSIDU HONNÊTE de
    l'inductivité, JAMAIS supposé vrai : il est transporté en antécédent de
    `frame_inductif`.  Sa preuve complète exige l'injectivité ET la surjectivité de
    ⋃φ en version chaîne (la fonctionnalité, elle, est close via
    union_chaine_fonctionnelle)."""
    vC = var(C)
    return pourtout(C, impl(chaine(G, E_set, vC, x, y, z),
                            existe(m, majorant(G, vC, var(m), E_set, x))))


# ════════════════════════════════════════════════════════════════════════════
#  (iii) FRAME-INDUCTIF — l'énoncé d'inductivité de 𝔉, SOUS les deux hypothèses
#        HONNÊTES « 𝔉 est ordonné » et « toute chaîne est majorée ».  CLOS.
#        Échafaudage qui branche le recollement sur la définition est_inductif.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.23-24 | PDF p.151  (« on vérifie aussitôt que 𝔐 est un ensemble inductif (cf. III, p. 20, Exemple 2) »)
def frame_inductif(E_set="E", C="C", m="m", x="x", y="y", z="z"):
    """{ est_ordre(Γ𝔉,𝔉), enonce_chaine_majoree(Γ𝔉,𝔉) } ⊢ est_inductif(Γ𝔉,𝔉).

    🎯 INDUCTIVITÉ du poset 𝔉 de l'argument de Zorn de Bourbaki (E.III.48 : « On
    vérifie aussitôt que 𝔐 est inductif »).  Par DÉFINITION (Déf. 3 §III.2),
    est_inductif(Γ𝔉,𝔉) = est_ordre(Γ𝔉,𝔉) ET (∀C)(chaine ⇒ (∃m)majorant) ; les deux
    conjoints sont EXACTEMENT les deux hypothèses honnêtes ici — l'ordre de 𝔉 et
    l'existence du majorant-recollement pour chaque chaîne.  AUCUNE n'est postulée
    vraie : transportées en antécédent.

    Une fois le résidu `enonce_chaine_majoree` fourni (recollement (⋃S,⋃φ)∈𝔉
    majorant — fonctionnalité close ici, injectivité/surjectivité chaîne à venir),
    `frame_inductif` livre l'hypothèse d'inductivité dont Zorn (`maximal_pair_existe`)
    a besoin.  CLOS (introduction de conjonction) ; conclusion ∉ hyps ; theorie=22."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import conjonction_intro
    vE = _t(E_set)
    Gam = frame_ordre(vE)                                  # Γ𝔉
    Fr = frame_pair(vE)                                    # 𝔉
    # est_inductif(Γ𝔉,𝔉) = est_ordre(Γ𝔉,𝔉) ET (∀C)(chaine ⇒ (∃m)majorant)
    h_ordre = N.assume(est_ordre(Gam, Fr, x, y, z))                 # HONNÊTE
    h_maj = N.assume(enonce_chaine_majoree(Gam, Fr, C, m, x, y, z)) # HONNÊTE
    res = conjonction_intro(h_ordre, h_maj)
    cible = est_inductif(Gam, Fr, C, m, x, y, z)
    assert res.conclusion == cible, "frame_inductif : ≠ est_inductif(Γ𝔉,𝔉)"
    assert res.conclusion not in res.hypotheses, "frame_inductif : VACUOUS"
    return res


__all__ = [
    # crux fonctionnel du recollement de chaîne (CLOS, via C60)
    "union_chaine_fonctionnelle", "union_chaine_valeur",
    # résidu honnête (existence du majorant-recollement) + énoncé d'inductivité
    "enonce_chaine_majoree", "frame_inductif",
]
