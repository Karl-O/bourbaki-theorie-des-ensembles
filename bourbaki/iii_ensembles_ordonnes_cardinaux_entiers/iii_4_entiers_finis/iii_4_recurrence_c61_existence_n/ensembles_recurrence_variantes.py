"""§III.4.3 — Remarque : les VARIANTES du principe de récurrence (E III.33-34).

Bourbaki : « On utilise souvent, sous le nom de "principe de récurrence",
divers critères qui se déduisent aisément de C61 » — quatre variantes :

  1) récurrence FORTE : S{n} := (∀p)((n entier et p entier et p<n) ⇒ R{p}) ;
     si S{n} entraîne R{n}, alors (∀n)(n entier ⇒ R{n}) ;
  2) récurrence À PARTIR DE k ;
  3) récurrence LIMITÉE À UN INTERVALLE (a ≤ n ≤ b) ;
  4) récurrence DESCENDANTE (de b vers a ; énoncé fin E III.33, suite E III.34).

STATUT : ÉNONCÉS FORMALISÉS (constructeurs de formules ci-dessous, sur une
relation R OPAQUE, callable Terme→Terme), DÉRIVATIONS NON FAITES (PARTIEL).
Les démonstrations du livre — poser S{n}, vérifier S{0} et S{n}⇒S{n+1}, puis
appliquer C61 (`principe_recurrence_preuve`, fichier voisin, CLOS) — sont
transcrites dans les docstrings ; les dériver = brancher ces S{n} sur C61
(chantier listé dans CAMPAGNE_TROUS).  Rien n'est postulé, aucun `Theoreme`.

« n entier » = est_fini(n) ; ≤ / < = inf_egal_card / inf_strict_card (ordre
cardinal du dépôt) ; n+1 = successeur(n).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, impl, pourtout)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    inf_egal_card, inf_strict_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §4.3 Rem.- | E III.33 L.1-3 | PDF p.136  (intro : divers critères déduits de C61)

# ── 1) Récurrence FORTE ──────────────────────────────────────────────────────
# @livre Ch.III §4.3 Rem.1 | E III.33 L.4-15 | PDF p.136
#   (récurrence forte ; démo L.8-15 [S{0} vraie ; S{n+1} ⇔ « S{n} et R{n} » via
#    Prop.2 §4.2 ; C61 sur S] : NON dérivée)
def s_recurrence_forte(R, n, p: str = "pfor") -> Terme:
    """S{n} := (∀p)((n entier et p entier et p<n) ⇒ R{p})  (E III.33 L.4-5).

    C'est la relation-pivot de la récurrence forte : « R vaut STRICTEMENT
    AVANT n »."""
    vn, vp = _t(n), var(p)
    return pourtout(p, impl(et(et(est_fini(vn), est_fini(vp)),
                               inf_strict_card(vp, vn)),
                            R(vp)))


def hypothese_recurrence_forte(R, n: str = "nfor", p: str = "pfor") -> Terme:
    """« S{n} entraîne R{n} » (E III.33 L.6), lu uniformément :
    (∀n)( S{n} ⇒ R{n} )."""
    vn = var(n)
    return pourtout(n, impl(s_recurrence_forte(R, vn, p), R(vn)))


def conclusion_recurrence(R, n: str = "nfor") -> Terme:
    """(∀n)((n est un entier) ⇒ R{n})  (E III.33 L.7) — la conclusion commune
    des variantes 1 et de C61 lui-même."""
    vn = var(n)
    return pourtout(n, impl(est_fini(vn), R(vn)))


# ── 2) Récurrence À PARTIR DE k ──────────────────────────────────────────────
# @livre Ch.III §4.3 Rem.2 | E III.33 L.16-26 | PDF p.136
#   (récurrence à partir de k ; démo L.20-26 [S{n} := (n≥k)⇒R{n}, disjonction
#    des cas, C61] : NON dérivée)
def hypothese_recurrence_depuis(R, k, n: str = "ndep") -> Terme:
    """R{k} et (∀n)((n entier et n≥k et R{n}) ⇒ R{n+1})  (E III.33 L.17)."""
    vk, vn = _t(k), var(n)
    return et(R(vk),
              pourtout(n, impl(et(et(est_fini(vn), inf_egal_card(vk, vn)),
                                  R(vn)),
                               R(successeur(vn)))))


def conclusion_recurrence_depuis(R, k, n: str = "ndep") -> Terme:
    """(∀n)((n entier et n≥k) ⇒ R{n})  (E III.33 L.19)."""
    vk, vn = _t(k), var(n)
    return pourtout(n, impl(et(est_fini(vn), inf_egal_card(vk, vn)), R(vn)))


# ── 3) Récurrence LIMITÉE À UN INTERVALLE ────────────────────────────────────
# @livre Ch.III §4.3 Rem.3 | E III.33 L.27-33 | PDF p.136
#   (récurrence limitée à l'intervalle a ≤ n ≤ b, a≤b ; démo L.32-33
#    [S{n} := (a≤n<b)⇒R{n}, comme la variante 2] : NON dérivée)
def hypothese_recurrence_intervalle(R, a, b, n: str = "nint") -> Terme:
    """R{a} et (∀n)((n entier et a≤n<b et R{n}) ⇒ R{n+1})  (E III.33 L.29)."""
    va, vb, vn = _t(a), _t(b), var(n)
    return et(R(va),
              pourtout(n, impl(et(et(et(est_fini(vn), inf_egal_card(va, vn)),
                                     inf_strict_card(vn, vb)),
                                  R(vn)),
                               R(successeur(vn)))))


def conclusion_recurrence_intervalle(R, a, b, n: str = "nint") -> Terme:
    """(∀n)((n entier et a≤n≤b) ⇒ R{n})  (E III.33 L.31)."""
    va, vb, vn = _t(a), _t(b), var(n)
    return pourtout(n, impl(et(et(est_fini(vn), inf_egal_card(va, vn)),
                               inf_egal_card(vn, vb)),
                            R(vn)))


# ── 4) Récurrence DESCENDANTE ────────────────────────────────────────────────
# @livre Ch.III §4.3 Rem.4 | E III.33 L.34-36 | PDF p.136
#   (récurrence descendante : R{b} et « R{n+1} ⇒ R{n} » sur a≤n<b ⇒ R sur
#    [a,b] ; l'énoncé se conclut et se démontre en E III.34 [page annotée par
#    ailleurs] : NON dérivée)
def hypothese_recurrence_descendante(R, a, b, n: str = "ndes") -> Terme:
    """R{b} et (∀n)((n entier et a≤n<b et R{n+1}) ⇒ R{n})  (E III.33 L.36)."""
    va, vb, vn = _t(a), _t(b), var(n)
    return et(R(vb),
              pourtout(n, impl(et(et(et(est_fini(vn), inf_egal_card(va, vn)),
                                     inf_strict_card(vn, vb)),
                                  R(successeur(vn))),
                               R(vn))))


def conclusion_recurrence_descendante(R, a, b, n: str = "ndes") -> Terme:
    """(∀n)((n entier et a≤n≤b) ⇒ R{n})  (E III.34) — même conclusion que la
    variante 3, l'induction descendant de b au lieu de monter de a."""
    return conclusion_recurrence_intervalle(R, a, b, n)


__all__ = [
    "s_recurrence_forte", "hypothese_recurrence_forte", "conclusion_recurrence",
    "hypothese_recurrence_depuis", "conclusion_recurrence_depuis",
    "hypothese_recurrence_intervalle", "conclusion_recurrence_intervalle",
    "hypothese_recurrence_descendante", "conclusion_recurrence_descendante",
]
