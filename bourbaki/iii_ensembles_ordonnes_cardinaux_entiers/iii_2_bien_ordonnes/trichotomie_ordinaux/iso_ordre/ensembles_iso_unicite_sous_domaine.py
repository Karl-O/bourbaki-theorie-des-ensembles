"""§III.2 — COROLLAIRE 1 / UNICITÉ, généralisé à un SOUS-DOMAINE S ⊆ E.

Variante « sous-domaine » du cœur algébrique de `ensembles_iso_unicite.py` :
un automorphisme d'ordre d'un sous-ensemble S d'un ensemble bien ordonné (E,R)
est l'identité SUR S.  Toute la machinerie route par le bon ordre AMBIANT
est_bien_ordonne(R,E) + inclus(S,E), JAMAIS la formule littérale bo(R,S) (qui est
FAUSSE pour un segment PROPRE S⊊E — cf. l'en-tête de
`ensembles_lemme4_sous_domaine.py`).

C'est l'analogue exact de `point_fixe_automorphisme` / `auto_iso_est_identite`,
mais chaque appel à `lemme_4(R,E,·)` devient `lemme_4_sous_domaine(R,E,S,·)`, les
appartenances « ∈E » deviennent « ∈S », et la borne dont on a besoin pour la
seconde instance du lemme est h(x)∈S (livrée par l'hypothèse de carte
(∀t)(t∈S⇒h(t)∈S)).  L'antisymétrie reste celle du bon ordre AMBIANT
(_antisym_de_bo(est_bien_ordonne(R,E))).

  • `point_fixe_automorphisme_sous_domaine` :
        { est_bien_ordonne(R,E),  inclus(S,E),
          (∀t)(t∈S ⇒ h(t)∈S),  h strict. croissante S→S,        [h : S→S iso]
          (∀t)(t∈S ⇒ k(t)∈S),  k strict. croissante S→S,        [k=h⁻¹ : S→S iso]
          (∀x)(x∈S ⇒ k(h(x))=x) }                                [k∘h = id_S]
        ⊢ (∀x)( x∈S ⇒ h(x) = x ).
    🎯 « Un automorphisme d'ordre d'un sous-ordre S est l'identité sur S », CŒUR
    algébrique — entièrement dérivé de lemme_4_sous_domaine + antisymétrie AMBIANTE.

  • `auto_iso_est_identite_sous_domaine` : emballage verbatim de Cor 1 (sous-domaine),
    réutilisant le cœur ci-dessus.

theorie_ensembles() RESTE = 22 (rien postulé : on RÉUTILISE lemme_4_sous_domaine —
lui-même sous theorie=22 + axiome dédié du mauvais ensemble — et l'antisymétrie du
bon ordre).  Valeur h(x) au sens Bourbaki, liant interne « j » (cohérent avec
lemme_4 / ordre monotone), via _val.  h,k acceptent des TERMES composés (c=φ'⁻¹∘φ).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import symetrie
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_lemme4_croissante import (
    _val, _R_de, _antisym_de_bo,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.lemme4_segments.ensembles_lemme4_sous_domaine import (
    lemme_4_sous_domaine, _f_dans_S,
)


def _t(t):
    return t if isinstance(t, Terme) else var(t)


def _leib(a, b, h_ab, phi_fun, h_phi_a, hole="hole_iso_sd"):
    """De  a=b  et  φ(a)  déduit  φ(b)  (Leibniz S6, trou `hole`)."""
    va, vb = _t(a), _t(b)
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import equivalence_avant
    eqv = N.modus_ponens(h_ab, N.s6(va, vb, hole, phi_fun(var(hole))))
    return N.modus_ponens(h_phi_a, equivalence_avant(eqv))


# ════════════════════════════════════════════════════════════════════════════
#  COR 1 (cœur, SOUS-DOMAINE) — un automorphisme d'ordre de S⊆E est l'identité sur S.
# ════════════════════════════════════════════════════════════════════════════
def point_fixe_automorphisme_sous_domaine(R="R", E_set="E", S="S", h="h", k="k", x="x"):
    """⊢ { est_bien_ordonne(R,E),  inclus(S,E),
           (∀t)(t∈S ⇒ h(t)∈S),  h strict. croissante S→S,
           (∀t)(t∈S ⇒ k(t)∈S),  k strict. croissante S→S,
           (∀x)(x∈S ⇒ k(h(x))=x) }
         ⊢ (∀x)( x∈S ⇒ h(x) = x ).

    🎯 CŒUR de Cor 1 §III.2 / unicité de l'iso, variante SOUS-DOMAINE.
    lemme_4_sous_domaine sur h : x ≤ h(x) pour x∈S.  lemme_4_sous_domaine sur k,
    instancié à h(x)∈S : h(x) ≤ k(h(x)).  Rétraction k(h(x))=x : donc h(x) ≤ x.
    Antisymétrie AMBIANTE (x ≤ h(x) et h(x) ≤ x) ⇒ x = h(x), i.e. h(x)=x.
    Tout le bon ordre est consommé par bo(R,E)+inclus(S,E), JAMAIS bo(R,S)."""
    vR, vE, vS, vh, vk = var(R), _t(E_set), _t(S), _t(h), _t(k)  # h,k acceptent un TERME composé
    Rf = _R_de(R)
    vx = var(x)
    hx = _val(vh, vx)                                          # h(x)

    # ── lemme_4_sous_domaine sur h : (∀x)(x∈S ⇒ R{x, h(x)}) ────────────────────
    l4h = lemme_4_sous_domaine(R, E_set, S, h)                 # {bo,inclus,h:S→S,h scr} ⊢ …
    Hx = N.assume(appartient(vx, vS))                          # x∈S
    Rx_hx = N.modus_ponens(Hx, instancie(l4h, vx))            # R{x, h(x)}

    # ── lemme_4_sous_domaine sur k, instancié à h(x)∈S ─────────────────────────
    l4k = lemme_4_sous_domaine(R, E_set, S, k)                 # {bo,inclus,k:S→S,k scr} ⊢ …
    Hhmap = N.assume(_f_dans_S(vh, vS))                       # (∀t)(t∈S⇒h(t)∈S)
    hx_in_S = N.modus_ponens(Hx, instancie(Hhmap, vx))       # h(x)∈S  (PAS ∈E)
    Rhx_khx = N.modus_ponens(hx_in_S, instancie(l4k, hx))    # R{h(x), k(h(x))}

    # ── rétraction : k(h(x)) = x ⇒ R{h(x), x} ─────────────────────────────────
    Hretr = N.assume(pourtout(x, impl(appartient(vx, vS),
                                      egal(_val(vk, hx), vx))))
    khx_eq_x = N.modus_ponens(Hx, instancie(Hretr, vx))      # k(h(x)) = x
    # transporter R{h(x), k(h(x))} le long de k(h(x))=x  →  R{h(x), x}
    Rhx_x = _leib(_val(vk, hx), vx, khx_eq_x,
                  lambda w: Rf(hx, w), Rhx_khx)               # R{h(x), x}

    # ── antisymétrie AMBIANTE : R{x,h(x)} et R{h(x),x} ⇒ x = h(x) ──────────────
    anti = _antisym_de_bo(E.est_bien_ordonne(Rf, vE))
    anti_inst = instancie(instancie(anti, vx), hx)
    x_eq_hx = N.modus_ponens(conjonction_intro(Rx_hx, Rhx_x), anti_inst)  # x = h(x)
    hx_eq_x = N.modus_ponens(x_eq_hx, symetrie(vx, hx))      # h(x) = x

    body = N.loi_deduction(appartient(vx, vS), hx_eq_x)      # x∈S ⇒ h(x)=x
    return N.generalisation(x, body)                         # (∀x)(x∈S ⇒ h(x)=x)


def point_fixe_automorphisme_sous_domaine_cible(R="R", E_set="E", S="S", h="h", k="k", x="x"):
    """ÉNONCÉ-cible (test miroir) de point_fixe_automorphisme_sous_domaine."""
    vS, vx, vh = var(S), var(x), var(h)
    return pourtout(x, impl(appartient(vx, vS), egal(_val(vh, vx), vx)))


# ════════════════════════════════════════════════════════════════════════════
#  COROLLAIRE 1 verbatim (SOUS-DOMAINE) — un automorphisme d'ordre de S⊆E est id_S.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §2.5 Cor.1 | E III.22 L.15-16 | PDF p.125  (Cor. 1 généralisé à un sous-domaine S ⊆ E, bon ordre ambiant)
def auto_iso_est_identite_sous_domaine(R="R", E_set="E", S="S", h="h", k="k", x="x"):
    """⊢ { est_bien_ordonne(R,E),  inclus(S,E),
           (∀t)(t∈S ⇒ h(t)∈S),  h strict. croissante S→S,
           (∀t)(t∈S ⇒ k(t)∈S),  k strict. croissante S→S,
           (∀x)(x∈S ⇒ k(h(x))=x) }
         ⊢ (∀x)( x∈S ⇒ h(x) = x ).

    🎯 COROLLAIRE 1 §III.2 (E.III.2.6) verbatim, variante SOUS-DOMAINE : un
    automorphisme d'ordre h : S ≅ S (sur S⊆E, S muni de l'ordre AMBIANT de E) est
    l'application identique de S.  h est strictement croissant, son inverse k aussi,
    avec k∘h=id_S ; le point fixe h(x)=x (x∈S) tombe de lemme_4_sous_domaine +
    antisymétrie AMBIANTE.  RÉUTILISE le cœur point_fixe_automorphisme_sous_domaine."""
    return point_fixe_automorphisme_sous_domaine(R, E_set, S, h, k, x)


def auto_iso_est_identite_sous_domaine_cible(R="R", E_set="E", S="S", h="h", k="k", x="x"):
    """ÉNONCÉ-cible (test miroir) de auto_iso_est_identite_sous_domaine."""
    return point_fixe_automorphisme_sous_domaine_cible(R, E_set, S, h, k, x)


__all__ = [
    "point_fixe_automorphisme_sous_domaine",
    "point_fixe_automorphisme_sous_domaine_cible",
    "auto_iso_est_identite_sous_domaine",
    "auto_iso_est_identite_sous_domaine_cible",
]
