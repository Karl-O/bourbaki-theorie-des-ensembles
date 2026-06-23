"""§III.2 — COROLLAIRE 1 / UNICITÉ (cœur algébrique) : un AUTOMORPHISME d'ordre
d'un bon ordre est l'IDENTITÉ ; d'où l'UNICITÉ de l'isomorphisme d'ordre entre
deux bons ordres (le « un et un seul » du Théorème 3, E.III.2.6).

Schéma fidèle Bourbaki (étape (c) du blueprint DESIGN_trichotomie_III2.md) : si
f, g sont deux iso d'ordre E→E', alors h := f∘g⁻¹ est un iso d'ordre E'→E', donc
strictement croissant, et son inverse k := g∘f⁻¹ aussi.  Le LEMME 4 (lemme_4,
déjà clos, b="yv") appliqué à h donne x ≤ h(x) pour tout x∈E' ; appliqué à k il
donne x ≤ k(x).  En l'instanciant à h(x) : h(x) ≤ k(h(x)) = x (rétraction
k∘h=id).  Avec x ≤ h(x) et l'ANTISYMÉTRIE du bon ordre, h(x)=x : f∘g⁻¹ = id_{E'},
donc f=g.

Ce module FERME le CŒUR de cette chaîne sous hypothèses EXPLICITES (fidèles, non
affaiblies) — l'assemblage géométrique f∘g⁻¹ (composée d'iso + réciproque, avec
alignement du liant de valeur yv↔y de compatible_ordre) reste un chantier de glue
REPORTÉ.  Les deux théorèmes ci-dessous sont CONDITIONNELS (hyps dans le séquent),
pas clos, et ce n'est ni une tautologie ni un énoncé affaibli :

  • `point_fixe_automorphisme` :
        { est_bien_ordonne(R,E),
          (∀t)(t∈E ⇒ h(t)∈E),  h strict. croissante E→E,           [h : E→E iso]
          (∀t)(t∈E ⇒ k(t)∈E),  k strict. croissante E→E,           [k=h⁻¹ : E→E iso]
          (∀x)(x∈E ⇒ k(h(x))=x) }                                  [k∘h = id_E]
        ⊢ (∀x)( x∈E ⇒ h(x) = x ).
    🎯 « Le seul automorphisme d'ordre d'un bon ordre est l'identité » (Cor 1
    verbatim), CŒUR algébrique — entièrement dérivé de lemme_4 + antisymétrie.

  • `iso_unicite_extensionnel` :
        { f∈𝓕(E',E),  g∈𝓕(E',E),
          (∀x)(x∈E' ⇒ valeur(graphe_de f,x) = valeur(graphe_de g,x)) }
        ⊢ f = g.
    « Deux iso d'ordre qui ont les mêmes valeurs sont égaux » : c'est le pas final
    f=g par extensionnalité des applications (application_egale_par_valeurs), qui
    consomme le point fixe h(x)=x une fois traduit en « f et g coïncident ».

theorie_ensembles() RESTE = 22 (rien postulé : on RÉUTILISE lemme_4 — lui-même
sous theorie=22 + axiome dédié du mauvais ensemble — et application_egale_par_valeurs).
Valeur f(x) au sens Bourbaki, liant interne « yv » (cohérent avec lemme_4 / ordre
monotone) — PAS de pont yv↔y ici.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
from bourbaki.cardinaux.ensembles_lemme4_croissante import (
    lemme_4, _val, _R_de, _antisym_de_bo, _f_dans_E,
)
from bourbaki.ensembles.fonctions.hors_ii_3.ii_5_produit_famille.ensembles_application_valeur import (
    application_egale_par_valeurs,
)
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.cardinaux.ensembles_composee_bijection import composee_bijection
from bourbaki.cardinaux.ensembles_bijection import reciproque_est_bijection
from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro as _conj_intro


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _leib(a, b, h_ab, phi_fun, h_phi_a, hole="hole_iso"):
    """De  a=b  et  φ(a)  déduit  φ(b)  (Leibniz S6, trou `hole`)."""
    va, vb = _t(a), _t(b)
    from bourbaki.logique.tactiques.tactiques_abrege2 import equivalence_avant
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, hole, phi_fun(var(hole))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  COR 1 (cœur) — un automorphisme d'ordre d'un bon ordre est l'identité.
# ════════════════════════════════════════════════════════════════════════════
def point_fixe_automorphisme(R="R", E_set="E", h="h", k="k", x="x"):
    """⊢ { est_bien_ordonne(R,E),
           (∀t)(t∈E ⇒ h(t)∈E),  h strict. croissante E→E,
           (∀t)(t∈E ⇒ k(t)∈E),  k strict. croissante E→E,
           (∀x)(x∈E ⇒ k(h(x))=x) }
         ⊢ (∀x)( x∈E ⇒ h(x) = x ).

    🎯 CŒUR de Cor 1 §III.2 / unicité de l'iso (le « un et un seul » du Th. 3).
    Lemme 4 sur h : x ≤ h(x).  Lemme 4 sur k, instancié à h(x)∈E : h(x) ≤ k(h(x)).
    Rétraction k(h(x))=x : donc h(x) ≤ x.  Antisymétrie (x ≤ h(x) et h(x) ≤ x)
    ⇒ x = h(x), i.e. h(x)=x."""
    vR, vE, vh, vk = var(R), _t(E_set), _t(h), _t(k)   # h,k acceptent un TERME composé (c=φ'⁻¹∘φ)
    Rf = _R_de(R)
    vx = var(x)
    hx = _val(vh, vx)                                           # h(x)

    # ── Lemme 4 sur h : (∀x)(x∈E ⇒ R{x, h(x)}) ─────────────────────────────────
    l4h = lemme_4(R, E_set, h)                                  # {bo, h:E→E, h scr} ⊢ …
    Hx = N.assume(appartient(vx, vE))                           # x∈E
    Rx_hx = N.modus_ponens(Hx, instancie(l4h, vx))             # R{x, h(x)}

    # ── Lemme 4 sur k : (∀x)(x∈E ⇒ R{x, k(x)}), instancié à h(x) ───────────────
    l4k = lemme_4(R, E_set, k)                                  # {bo, k:E→E, k scr} ⊢ …
    Hhmap = N.assume(_f_dans_E(vh, vE))                        # (∀t)(t∈E⇒h(t)∈E)
    hx_in_E = N.modus_ponens(Hx, instancie(Hhmap, vx))        # h(x)∈E
    Rhx_khx = N.modus_ponens(hx_in_E, instancie(l4k, hx))     # R{h(x), k(h(x))}

    # ── rétraction : k(h(x)) = x ⇒ R{h(x), x} ──────────────────────────────────
    Hretr = N.assume(pourtout(x, impl(appartient(vx, vE),
                                      egal(_val(vk, hx), vx))))
    khx_eq_x = N.modus_ponens(Hx, instancie(Hretr, vx))       # k(h(x)) = x
    # transporter R{h(x), k(h(x))} le long de k(h(x))=x  →  R{h(x), x}
    Rhx_x = _leib(_val(vk, hx), vx, khx_eq_x,
                  lambda w: Rf(hx, w), Rhx_khx)                # R{h(x), x}

    # ── antisymétrie : R{x,h(x)} et R{h(x),x} ⇒ x = h(x) ───────────────────────
    anti = _antisym_de_bo(E.est_bien_ordonne(Rf, vE))
    anti_inst = instancie(instancie(anti, vx), hx)
    x_eq_hx = N.modus_ponens(conjonction_intro(Rx_hx, Rhx_x), anti_inst)  # x = h(x)
    hx_eq_x = N.modus_ponens(x_eq_hx, symetrie(vx, hx))        # h(x) = x

    body = N.loi_deduction(appartient(vx, vE), hx_eq_x)        # x∈E ⇒ h(x)=x
    return N.generalisation(x, body)                           # (∀x)(x∈E ⇒ h(x)=x)


def point_fixe_automorphisme_cible(R="R", E_set="E", h="h", k="k", x="x"):
    """ÉNONCÉ-cible (test miroir) de la conclusion de point_fixe_automorphisme."""
    vE, vx, vh = var(E_set), var(x), var(h)
    return pourtout(x, impl(appartient(vx, vE), egal(_val(vh, vx), vx)))


# ════════════════════════════════════════════════════════════════════════════
#  UNICITÉ EXTENSIONNELLE — deux applications de mêmes valeurs sont égales.
#  (Pas final f=g, à partir du point fixe traduit en « mêmes valeurs ».)
# ════════════════════════════════════════════════════════════════════════════
def iso_unicite_extensionnel(f="f", g="g", Ep="Ep", E_set="E"):
    """⊢ { f∈𝓕(E',E), g∈𝓕(E',E),
           (∀x)(x∈E' ⇒ valeur(graphe_de f,x)=valeur(graphe_de g,x)) } ⊢ f = g.

    PAS FINAL de l'unicité : une fois établi que f et g (iso d'ordre de E' dans E)
    ont les MÊMES VALEURS sur E' (ce que livre point_fixe_automorphisme via
    f∘g⁻¹=id), l'extensionnalité des applications (application_egale_par_valeurs,
    E.II.5.2) conclut f = g.  Pur emballage RÉUTILISÉ (aucun axiome ajouté)."""
    return application_egale_par_valeurs(f, g, Ep, E_set)


def iso_unicite_extensionnel_cible(f="f", g="g", Ep="Ep", E_set="E"):
    """ÉNONCÉ-cible (test miroir) de iso_unicite_extensionnel."""
    return egal(_t(f), _t(g))


# ════════════════════════════════════════════════════════════════════════════
#  ROUTE BIJECTION (pièce d'assemblage) — f∘g⁻¹ : E'→E' est une bijection.
#  Au NIVEAU bijection (est_bijection_de à 4 conjoints), via composee_bijection +
#  reciproque_est_bijection.  Le passage à est_bijective de l'iso d'ordre, et le
#  raccord du liant de valeur (yv↔y) de compatible_ordre, restent REPORTÉS.
# ════════════════════════════════════════════════════════════════════════════
def reciproque_bijection_role(g="g", E_set="E", Ep="Ep"):
    """⊢ est_bijection_de(g,E,E') ⇒ est_bijection_de(g⁻¹,E',E).

    g⁻¹ joue le rôle de l'inverse pour la composée f∘g⁻¹ : E'→E' (Prop. 7, E.II.3.7).
    Pur RÉUTILISÉ de reciproque_est_bijection (rien postulé)."""
    return reciproque_est_bijection(g, E_set, Ep)


def compose_bijection_automorphisme(f="f", k="k", Ep="Ep", E_set="E"):
    """⊢ { est_bijection_de(k,E',E),  est_bijection_de(f,E,E') }
         ⊢ est_bijection_de(f∘k, E', E').

    PIÈCE D'ASSEMBLAGE de l'unicité : avec k=g⁻¹ (rôle fourni par
    reciproque_bijection_role), la composée h := f∘k est une bijection E'→E' (donc
    candidate automorphisme).  Via composee_bijection (composée de deux bijections,
    déjà close) : F:=k (E'→E), G:=f (E→E'), G∘F = f∘k : E'→E'.  RÉUTILISÉ, rien
    postulé.  (k abstrait — nommé — car composee_bijection est indexée par des NOMS
    de variables, pas des termes composites comme g⁻¹ ; le branchement k:=g⁻¹ se
    fait par reciproque_bijection_role.)"""
    vf, vk, vEp, vE = _t(f), _t(k), _t(Ep), _t(E_set)
    comp_imp = composee_bijection(k, f, Ep, E_set, Ep)   # (bij(k,E',E) et bij(f,E,E')) ⇒ bij(f∘k,E',E')
    Hk = N.assume(est_bijection_de(vk, vEp, vE))
    Hf = N.assume(est_bijection_de(vf, vE, vEp))
    return N.modus_ponens(_conj_intro(Hk, Hf), comp_imp)


def compose_bijection_automorphisme_cible(f="f", k="k", Ep="Ep", E_set="E"):
    """ÉNONCÉ-cible (test miroir) de compose_bijection_automorphisme."""
    vf, vk, vEp = _t(f), _t(k), _t(Ep)
    return est_bijection_de(E.composee(vf, vk), vEp, vEp)


__all__ = [
    "point_fixe_automorphisme", "point_fixe_automorphisme_cible",
    "iso_unicite_extensionnel", "iso_unicite_extensionnel_cible",
    "reciproque_bijection_role",
    "compose_bijection_automorphisme", "compose_bijection_automorphisme_cible",
]
