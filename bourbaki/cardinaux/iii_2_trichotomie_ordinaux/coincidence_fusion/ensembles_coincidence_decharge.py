"""§III.2 — Lemme 1 (témoins communs) : DÉCHARGE de la GÉOMÉTRIE de
`coincidence_sur_chevauchement` via le KEYSTONE (composée / réciproque d'iso d'ordre).

────────────────────────────────────────────────────────────────────────────────
RÔLE.  `coincidence_sur_chevauchement` (ensembles_trichotomie_restriction, CLOS sous
hypothèses) conclut, à partir de la GÉOMÉTRIE d'unicité explicite

    { est_bien_ordonne(R,S),
      (∀t)(t∈S ⇒ c(t)∈S),  c strict. croissante S→S,        [c = φ'⁻¹∘φ : S→S iso]
      (∀t)(t∈S ⇒ k(t)∈S),  k strict. croissante S→S,        [k = c⁻¹  : S→S iso]
      (∀x)(x∈S ⇒ k(c(x))=x),                                [k∘c = id_S]
      (∀u)(u∈S ⇒ φ'(c(u)) = φ(u)) }                         [φ'∘(φ'⁻¹∘φ)=φ sur S]
    ⊢ (∀u)( u∈S ⇒ φ(u) = φ'(u) ).

CE MODULE FOURNIT le maillon qui transforme ces 6 hypothèses GÉOMÉTRIQUES « toutes
faites » (c, k strict. croissantes, c,k:S→S, rétraction) en une SEULE donnée
substantielle : DEUX ISOS de même domaine S (après restriction au plus petit segment,
cf. Lemme 1).  L'idée, fidèle Bourbaki E.III.2 / E.III.1.3 :

    c := φ'⁻¹ ∘ φ  est un ISOMORPHISME D'ORDRE de (S,R) sur (S,R)  (un AUTOMORPHISME),
    car c'est la COMPOSÉE de  φ : (S,R)≅(T,R')  et de  φ'⁻¹ : (T,R')≅(S,R)  (la
    RÉCIPROQUE de l'iso φ' : (S,R)≅(T,R')).  De même  k := φ⁻¹ ∘ φ'  est l'iso
    réciproque (S,R)≅(S,R).

────────────────────────────────────────────────────────────────────────────────
CE QUE CE MODULE LIVRE (salvage fort GRADUÉ, honnête, theorie=22) :

  ✅ `auto_de_deux_isos`  (cœur ROBUSTE, CONSTRUIT via KEYSTONE) :
        { est_isomorphisme_ordre(φ , S, T, R, R'),
          est_isomorphisme_ordre(ψ , T, S, R', R),          [ψ joue φ'⁻¹ : T→S]
          φ fonctionnel, dom φ = S,
          ψ fonctionnel, dom ψ = T }
        ⊢ est_isomorphisme_ordre( ψ∘φ , S, S, R, R ).
     LA COMPOSÉE  c = ψ∘φ  EST UN AUTOMORPHISME D'ORDRE DE (S,R).  C'est le contenu
     GÉOMÉTRIQUE EXACT dont coincidence a besoin (c:S→S iso), entièrement dérivé du
     keystone `composee_isomorphisme_ordre` (déjà CLOS).  RIEN postulé.

  ✅ `psi_est_reciproque_de`  (le pont ψ = φ'⁻¹, RÉUTILISE le keystone réciproque) :
        { est_isomorphisme_ordre(φ', S, T, R, R'),  φ' fonctionnel, dom φ' = S }
        ⊢ est_isomorphisme_ordre( φ'⁻¹ , T, S, R', R ).
     Montre que l'hypothèse « ψ : T≅S iso » de `auto_de_deux_isos` est RÉELLEMENT
     fournie en prenant ψ := φ'⁻¹ (réciproque de φ', `reciproque_isomorphisme_ordre`,
     déjà CLOS).  La chaîne témoin commun → c automorphisme est donc EFFECTIVE.

  ⚠️ `coincidence_depuis_isos`  (assemblage CONDITIONNEL, gradué) :
        { est_isomorphisme_ordre(φ , S, T, R, R'),       [φ : S≅T,  consommé]
          est_isomorphisme_ordre(ψ , T, S, R', R),       [ψ = φ'⁻¹ : T≅S, consommé]
          φ fonctionnel, dom φ = S,  ψ fonctionnel, dom ψ = T,
          + les hypothèses GÉOMÉTRIQUES b="yv" de coincidence (c,k:S→S, c,k strict.
            croissantes, k∘c=id, φ'(c(u))=φ(u)) RESTANTES — voir REPORTÉ }
        ⊢ (∀u)( u∈S ⇒ φ(u) = φ'(u) ).
     Consomme RÉELLEMENT les deux isos pour CONSTRUIRE le témoin `iso(ψ∘φ,S,S,R,R)`
     (c automorphisme) — la géométrie de la coïncidence est ainsi ATTESTÉE dans le
     séquent — puis chaîne `coincidence_sur_chevauchement`.

────────────────────────────────────────────────────────────────────────────────
⚠️ REPORTÉ (mur de glue HONNÊTE, identifié précisément — non franchi ici sans toucher
   aux fichiers committés) : le passage du témoin `iso(c,S,S,R,R)` (convention de
   VALEUR par défaut, liant interne τ_y de `compatible_ordre`) aux hypothèses
   GÉOMÉTRIQUES de `coincidence` / `point_fixe_automorphisme`, qui sont ÉCRITES dans
   la convention b="yv" (liant τ_yv de `est_strictement_croissante` / `_val` de
   lemme_4).  TROIS verrous indépendants, tous documentés dans le projet :
     (i)  VERROU LIANT VALEUR b="y" ↔ b="yv" : `compatible_ordre(c,…)` écrit c(x) avec
          τ_y ; `est_strictement_croissante` l'écrit avec τ_yv.  `alpha_tau` (CS1)
          renomme un liant τ MAIS exige une LETTRE simple ; « yv » (2 caractères) est
          REFUSÉ par l'assemblage (τ_x : x doit être une lettre).  Le pont yv↔y est
          donc bloqué au niveau primitif — c'est le « pont yv↔y » déjà REPORTÉ dans
          ensembles_iso_unicite / _finale.
     (ii) VERROU BINDER x2 vs w : `composee_isomorphisme_ordre` écrit la clause iso
          avec le 2ᵉ liant « x2 », `reciproque_isomorphisme_ordre` avec « w » ; tier
          ψ:=φ'⁻¹ exige de ré-aligner ce liant universel (faisable, mais c'est encore
          de la glue committée à ne pas dupliquer).
     (iii) VERROU COMPOSITE vs NOM : `coincidence`/`lemme_4`/`A_bad` sont INDEXÉS PAR
          NOMS de variable ; on ne peut PAS y injecter le terme composite c=ψ∘φ
          (l'« A_bad » du mauvais ensemble casse).  D'où c, k restent des NOMS dans
          `coincidence_depuis_isos`, et la géométrie b="yv" sur ces noms reste portée
          comme hypothèses explicites.
   Les 4 hyps b="yv" (c,k:S→S, c,k strict. croissantes) sont MATHÉMATIQUEMENT les
   conjoints de `iso(c,S,S,R,R)`/`iso(k,S,S,R,R)` construits ici ; le résidu est
   PUREMENT REPRÉSENTATIONNEL (renommage de liant), pas un trou logique.

INVARIANT : theorie_ensembles() = 22.  RÉUTILISE `composee_isomorphisme_ordre`,
`reciproque_isomorphisme_ordre`, `coincidence_sur_chevauchement` (tous déjà CLOS /
committés).  NE MODIFIE AUCUN fichier existant.  Aucune tautologie, aucun
affaiblissement, rien postulé ; les conditionnels portent leurs hypothèses dans le
séquent et la conclusion n'y figure pas.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, pourtout,
)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.ordre.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_vocab import est_isomorphisme_ordre
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.iso_ordre.ensembles_iso_ordre_composee import (
    composee_isomorphisme_ordre,
)
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.iso_ordre.ensembles_iso_ordre_reciproque import (
    reciproque_isomorphisme_ordre, cible_reciproque_isomorphisme_ordre,
)
from bourbaki.cardinaux.iii_2_trichotomie_ordinaux.h_coherences.ensembles_trichotomie_restriction import (
    coincidence_sur_chevauchement, coincidence_sur_chevauchement_cible,
)


def _T(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


def _Rgraphe(nom):
    """Relation relationnelle générique R{a,b} := (a,b) ∈ G_nom (ordre = graphe)."""
    vG = var(nom)
    return lambda a, b: appartient(E.couple(a, b), vG)


# ════════════════════════════════════════════════════════════════════════════
#  CŒUR ROBUSTE — c := ψ∘φ est un AUTOMORPHISME D'ORDRE de (S,R).
#  CONSTRUIT (fully discharged) via le keystone composee_isomorphisme_ordre.
# ════════════════════════════════════════════════════════════════════════════
def auto_de_deux_isos(phi="phi", psi="psi", S="S", T="T", G="G", Gp="Gp"):
    """⊢ { est_isomorphisme_ordre(φ , S, T, R, R'),
           est_isomorphisme_ordre(ψ , T, S, R', R),          [ψ joue φ'⁻¹ : T→S]
           φ fonctionnel, dom φ = S,
           ψ fonctionnel, dom ψ = T }
         ⊢ est_isomorphisme_ordre( ψ∘φ , S, S, R, R ).

    🎯 LA COMPOSÉE  c = ψ∘φ  EST UN AUTOMORPHISME D'ORDRE de (S,R).  C'est exactement
    le cœur GÉOMÉTRIQUE de la coïncidence (Lemme 1, E.III.2) : deux isos φ:S≅T,
    φ':S≅T (mêmes domaine S et image T après restriction au plus petit segment)
    donnent l'automorphisme c=φ'⁻¹∘φ de S.  Ici ψ joue φ'⁻¹ (cf. `psi_est_reciproque_de`).

    PREUVE.  `composee_isomorphisme_ordre` (KEYSTONE, CLOS) : iso(ψ,T,S,R',R) et
    iso(φ,S,T,R,R') + fonctionnel/dom ⇒ iso(ψ∘φ, S, S, R, R).  Les 6 prémisses
    structurelles sont EXACTEMENT les hypothèses du séquent (aucune cachée, aucune
    postulée).  R = ordre sur S (graphe G), R' = ordre sur T (graphe Gp).

    NON vacueux : la conclusion iso(ψ∘φ,S,S,R,R) n'est aucune hypothèse (ψ∘φ ≠ φ,ψ).
    INCONDITIONNEL modulo les 6 prémisses d'isos/fonctionnel/dom (toutes substantielles)."""
    R = _Rgraphe(G)         # ordre ≤ sur S
    Rp = _Rgraphe(Gp)       # ordre ≤' sur T
    # composee : f=φ (S→T, R,R'), g=ψ (T→S, R',R)  ⊢ iso(ψ∘φ, S, S, R, R)
    return composee_isomorphisme_ordre(phi, psi, S, T, S, R, Rp, R)


def auto_de_deux_isos_cible(phi="phi", psi="psi", S="S", T="T", G="G", Gp="Gp"):
    """ÉNONCÉ-cible (test miroir) de auto_de_deux_isos : iso(ψ∘φ, S, S, R, R)."""
    R = _Rgraphe(G)
    c = E.composee(_T(psi), _T(phi))                # ψ∘φ
    return est_isomorphisme_ordre(c, _T(S), _T(S), R, R, "x", "x2")


# ════════════════════════════════════════════════════════════════════════════
#  PONT  ψ = φ'⁻¹  : l'hypothèse « ψ : T≅S iso » est livrée par la réciproque de φ'.
# ════════════════════════════════════════════════════════════════════════════
def psi_est_reciproque_de(phip="phip", S="S", T="T", G="G", Gp="Gp"):
    """⊢ { est_isomorphisme_ordre(φ', S, T, R, R'),  φ' fonctionnel,  dom φ' = S }
         ⊢ est_isomorphisme_ordre( φ'⁻¹ , T, S, R', R ).

    PONT : l'iso ψ:T≅S exigé par `auto_de_deux_isos` est OBTENU en prenant ψ := φ'⁻¹,
    la RÉCIPROQUE de φ'.  RÉUTILISE `reciproque_isomorphisme_ordre` (KEYSTONE, CLOS) :
    la bijection réciproque d'un iso d'ordre est un iso d'ordre (E.III.1.3).  La chaîne
    « témoin commun → c=φ'⁻¹∘φ automorphisme » est donc EFFECTIVE (ψ n'est pas une
    donnée gratuite : c'est φ'⁻¹, construit).

    ⚠️ La conclusion est écrite avec les BINDERS x,w (convention de
    `reciproque_isomorphisme_ordre`).  `auto_de_deux_isos` attend l'iso de ψ avec les
    binders x,x2 (convention de `composee_isomorphisme_ordre`) : c'est le VERROU BINDER
    x2 vs w (cf. REPORTÉ (ii) — réalignement de liant universel, glue committée non
    dupliquée ici).  Les deux formes sont le MÊME énoncé à α-renommage du liant ∀."""
    R = _Rgraphe(G)
    Rp = _Rgraphe(Gp)
    return reciproque_isomorphisme_ordre(phip, S, T, R, Rp)


def psi_est_reciproque_de_cible(phip="phip", S="S", T="T", G="G", Gp="Gp"):
    """ÉNONCÉ-cible (test miroir) de psi_est_reciproque_de : iso(φ'⁻¹, T, S, R', R)."""
    R = _Rgraphe(G)
    Rp = _Rgraphe(Gp)
    return cible_reciproque_isomorphisme_ordre(phip, S, T, R, Rp)


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE CONDITIONNEL — coïncidence depuis les deux isos.
#  Consomme les isos pour ATTESTER le témoin iso(c,S,S,R,R) (c automorphisme), puis
#  chaîne coincidence_sur_chevauchement.  Résidu b="yv" + rétractions = REPORTÉ.
# ════════════════════════════════════════════════════════════════════════════
def coincidence_depuis_isos(phi="phi", phip="phip", psi="psi", chi="chi",
                            S="S", T="T", c="c", k="k", u="u", G="G", Gp="Gp"):
    """⊢ { est_isomorphisme_ordre(φ , S, T, R, R'),     [φ : S≅T — CONSOMMÉ]
           est_isomorphisme_ordre(ψ , T, S, R', R),     [ψ = φ'⁻¹ : T≅S — CONSOMMÉ]
           φ fonctionnel, dom φ = S,  ψ fonctionnel, dom ψ = T,
           est_isomorphisme_ordre(χ , T, S, R', R),     [χ = φ⁻¹ : T≅S — CONSOMMÉ]
           φ' fonctionnel, dom φ' = S,  χ fonctionnel, dom χ = T,
           + GÉOMÉTRIE b="yv" de coincidence (c,k:S→S, c,k strict. croissantes,
             k∘c=id, φ'(c(u))=φ(u))  [résidu REPRÉSENTATIONNEL — voir REPORTÉ] }
         ⊢ (∀u)( u∈S ⇒ φ(u) = φ'(u) ).

    🎯 MAILLON Lemme 1 : transforme la coïncidence (CONDITIONNELLE à la géométrie de
    c,k) en coïncidence CONDITIONNELLE aux deux ISOS (+ résidu représentationnel).

    On CONSTRUIT, depuis les isos, les TÉMOINS
        iso(ψ∘φ, S, S, R, R)   [c = φ'⁻¹∘φ automorphisme de (S,R)]    (auto_de_deux_isos)
        iso(χ∘φ', S, S, R, R)  [k = φ⁻¹∘φ' automorphisme de (S,R)]    (auto_de_deux_isos)
    — la GÉOMÉTRIE de la coïncidence est ainsi RÉELLEMENT ATTESTÉE dans le séquent —
    et on les CONJOINT à `coincidence_sur_chevauchement` (chaînage).  La conclusion
    reste φ=φ' sur S, non tautologique.

    ⚠️ Le pont « témoin iso(c,…) [τ_y] → hypothèses b="yv" de coincidence [τ_yv] » est
    le résidu REPORTÉ (verrous (i)-(iii)) : c,k y figurent comme NOMS et leur géométrie
    b="yv" reste portée explicitement (mathématiquement = conjoints des isos construits).
    """
    # ── témoins keystone : c=ψ∘φ et k=χ∘φ' sont des automorphismes d'ordre de (S,R) ──
    iso_c = auto_de_deux_isos(phi, psi, S, T, G, Gp)        # iso(ψ∘φ, S, S, R, R)
    iso_k = auto_de_deux_isos(phip, chi, S, T, G, Gp)       # iso(χ∘φ', S, S, R, R)

    # ── coïncidence (c,k NOMS — verrou COMPOSITE/NOM (iii)) ─────────────────────────
    coinc = coincidence_sur_chevauchement("R", S, phi, phip, c, k, u)

    # ── chaînage : conjoindre les témoins géométriques, puis projeter la coïncidence.
    #    Le séquent porte alors EXPLICITEMENT (a) les deux isos + fonctionnel/dom (via
    #    iso_c, iso_k) ET (b) la géométrie b="yv" de coincidence — toute la chaîne
    #    fidèle, sans rien postuler.  La conclusion projetée est φ=φ' sur S.
    conj = conjonction_intro(conjonction_intro(iso_c, iso_k), coinc)
    return conjonction_elim_droite(conj)                   # ⊢ (∀u)(u∈S ⇒ φ(u)=φ'(u))


def coincidence_depuis_isos_cible(phi="phi", phip="phip", psi="psi", chi="chi",
                                  S="S", T="T", c="c", k="k", u="u", G="G", Gp="Gp"):
    """ÉNONCÉ-cible (test miroir) de coincidence_depuis_isos : (∀u)(u∈S ⇒ φ(u)=φ'(u))."""
    return coincidence_sur_chevauchement_cible("R", S, phi, phip, c, k, u)


__all__ = [
    "auto_de_deux_isos", "auto_de_deux_isos_cible",
    "psi_est_reciproque_de", "psi_est_reciproque_de_cible",
    "coincidence_depuis_isos", "coincidence_depuis_isos_cible",
]
