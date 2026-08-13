"""§III.6.3 — Théorème 2 (HESSENBERG, Zorn E.III.48) : TENTATIVE de décharge des
DEUX résidus honnêtes de `frame_a_maximal` (𝔉≠∅ et frame-inductivité), et exposé
PRÉCIS du résidu irréductible (le BASE-CASE de Zorn / Lemmes 1-2 de Hessenberg).

────────────────────────────────────────────────────────────────────────────────
ÉTAT (mission « frame-maximal-clos », 2026-06-22).

`frame_a_maximal(E)` (`ensembles_frame_a_maximal.py`) ⊢ (∃m) element_maximal(Γ𝔉,𝔉,m)
sous EXACTEMENT 2 hypothèses honnêtes (vérifié : est_clos=False, theorie=22) :

  H1 = (∃x)(x ∈ 𝔉(E))                                       — 𝔉(E) ≠ ∅            (base de Zorn)
  H2 = (∀C)( (⋃S(C), ⋃φ(C)) ∈ 𝔉(E) )                       — frame-inductivité   (m_dans_frame_universel)

  ┌─ D1 — décharge de H1 (𝔉(E)≠∅) ──────────────────────────────────────────────┐
  │ Exhiber un membre concret de 𝔉(E) demande, par `_corps_frame`, un couple    │
  │ (S,φ) avec S⊂E, S INFINI et φ : S×S → S BIJECTIVE.  Une telle bijection EST  │
  │ a²=a pour S — circulaire, SAUF si S est un sous-ensemble DÉNOMBRABLE concret │
  │ avec la bijection dénombrable ℕ×ℕ≃ℕ (base-case de Bourbaki E.III.48).        │
  │ Or DANS LE DÉPÔT :                                                            │
  │   • « E infini ⊃ un D équipotent à ℕ » (LEMME 1) — ABSENT.                    │
  │   • « ℕ×ℕ ≃ ℕ » / ℵ₀·ℵ₀=ℵ₀ (LEMME 2) — ABSENT (arith. cardinale INFINIE,     │
  │     explicitement REPORTÉE, cf. ensembles_infinis_iii6.py).                   │
  │ ⇒ D1 N'EST PAS DÉCHARGEABLE honnêtement ici.  H1 = RÉSIDU base-case de Zorn.  │
  └──────────────────────────────────────────────────────────────────────────────┘

  ┌─ D2 — décharge de H2 (frame-inductivité) ───────────────────────────────────┐
  │ `union_chaine_dans_frame` (`ensembles_chaine_frame_membership.py`) ne livre  │
  │ (⋃S,⋃φ)∈𝔉 que SOUS hyps honnêtes (US⊂E, US infini, dom/inj/img-valeur du     │
  │ recollement).  Et `frame_inductif_chaine` documente l'OBSTRUCTION EXACTE :    │
  │   • A : C universellement quantifiée ⇒ ⋃S=⋃pr₁(C), ⋃φ=⋃pr₂(C) sont des       │
  │     FONCTIONS de C ; la construction « union des projections des membres »    │
  │     (familles indexées par les membres de C) n'est PAS disponible.            │
  │   • B : `frame_ordre` est un terme OPAQUE SANS axiome d'appartenance          │
  │     (pas d'`axiome_frame_ordre`) ⇒ (x,m)∈Γ𝔉 inétablissable.                   │
  │ ⇒ D2 N'EST PAS DÉCHARGEABLE honnêtement ici.  H2 = RÉSIDU inductivité.        │
  └──────────────────────────────────────────────────────────────────────────────┘

CONCLUSION DE LA MISSION.  Les DEUX résidus H1, H2 sont le BASE-CASE de Zorn et la
FRAME-INDUCTIVITÉ — tous deux butant sur les LEMMES 1-2 de Hessenberg (E infini ⊃ ℕ,
ℕ×ℕ≃ℕ) et la construction d'unions de projections de chaîne abstraite, ABSENTS du
dépôt (arithmétique cardinale INFINIE non encore développée).  Ils sont HONNÊTES,
SATISFIABLES (VRAIS dans l'argument de Bourbaki E.III.48) et E-niveau (variables
libres ⊆ {E}).  Ils ne peuvent être déchargés sans un vrai sous-chantier (Lemmes 1-2
+ familles indexées par chaîne) ; ils ne sont JAMAIS postulés vrais.

Ce module fournit donc :
  • `frame_a_maximal_clos(E)`            = `frame_a_maximal(E)` (les 2 résidus exposés,
                                          theorie=22) — pas de progrès de décharge possible.
  • `hessenberg_a_carre_egal_a_0hyp(E)` = `hessenberg_a_carre_egal_a_REEL(E)`, ⊢
                                          enonce_hessenberg(E) sous EXACTEMENT les 2 mêmes
                                          résidus de Zorn (est_clos=False, theorie=22).
  • `residus_honnetes(E)`               = la liste explicite [H1, H2] (pour audit/tests).

a²=a est donc prouvé MODULO le base-case de Zorn (Lemmes 1-2) — NON encore 0-hyp.

INVARIANT : theorie_ensembles() = 22 ; aucun axiome ; RIEN postulé ; noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, existe, pourtout, appartient, libres_f
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
#  Les 2 résidus honnêtes EXPLICITES (énoncés-formules, pour audit / tests).
# ════════════════════════════════════════════════════════════════════════════
def residu_H1(E_set="E", x="x"):
    """H1 = (∃x)(x ∈ 𝔉(E))  —  « 𝔉(E) ≠ ∅ »  (base-case de Zorn ; Lemmes 1-2)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair
    return existe(x, appartient(var(x), frame_pair(_t(E_set))))


def residu_H2(E_set="E", C="C"):
    """H2 = (∀C)( (⋃S(C), ⋃φ(C)) ∈ 𝔉(E) )  —  frame-inductivité (m_dans_frame_universel)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_inductif_assemblage import (
        m_dans_frame_universel,
    )
    return m_dans_frame_universel(E_set, C)


def residus_honnetes(E_set="E"):
    """Liste explicite [H1, H2] des 2 résidus honnêtes irréductibles."""
    return [residu_H1(E_set), residu_H2(E_set)]


# ════════════════════════════════════════════════════════════════════════════
#  frame_a_maximal_clos — re-export de frame_a_maximal avec audit des résidus.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Demo.2 | E III.48 L.24-25 | PDF p.151  (élément maximal de 𝔐 par Zorn, résidus honnêtes H1/H2 explicités)
def frame_a_maximal_clos(E_set="E"):
    """⊢ (∃m) element_maximal(Γ𝔉(E),𝔉(E),m)  sous EXACTEMENT les 2 résidus honnêtes
    H1 (𝔉(E)≠∅) et H2 (frame-inductivité).  NON 0-hyp : les 2 résidus butent sur le
    base-case de Zorn (Lemmes 1-2 de Hessenberg, ABSENTS du dépôt — voir docstring du
    module).  theorie=22 ; rien postulé ; conclusion ∉ hyps."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_a_maximal import frame_a_maximal
    res = frame_a_maximal(E_set)

    # ACCEPTANCE : exactement les 2 résidus honnêtes, E-niveau, conclusion ∉ hyps.
    H1, H2 = residu_H1(E_set), residu_H2(E_set)
    hyps = set(res.hypotheses)
    assert H1 in hyps, "frame_a_maximal_clos : H1 (𝔉≠∅) absente"
    assert H2 in hyps, "frame_a_maximal_clos : H2 (inductivité) absente"
    assert hyps == {H1, H2}, \
        "frame_a_maximal_clos : hyps inattendues\n" + "\n".join(str(h) for h in hyps)
    for h in res.hypotheses:
        assert set(libres_f(h)) <= {E_set}, \
            f"frame_a_maximal_clos : hyp non E-niveau\n{h}"
    assert res.conclusion not in res.hypotheses, "frame_a_maximal_clos : VACUOUS"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  hessenberg_a_carre_egal_a_0hyp — a²=a sous les 2 mêmes résidus de Zorn.
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §6.3 Th.2 | E III.47 L.30-32 | PDF p.150
def hessenberg_a_carre_egal_a_0hyp(E_set="E"):
    """🎯 ⊢ est_infini(Card E) ⇒ Card E·Card E = Card E  (enonce_hessenberg(E)),
    sous EXACTEMENT les 2 résidus honnêtes de Zorn (H1=𝔉≠∅, H2=frame-inductivité).

    = `hessenberg_a_carre_egal_a_REEL(E)` (conclusion E-seule, tous témoins éliminés,
    lock absent).  NON est_clos=True : les 2 résidus butent sur les Lemmes 1-2 de
    Hessenberg (E infini ⊃ ℕ ; ℕ×ℕ≃ℕ), ABSENTS du dépôt (arith. cardinale INFINIE
    non développée).  a²=a est donc prouvé MODULO le base-case de Zorn, PAS 0-hyp.
    theorie=22 ; rien postulé ; conclusion ∉ hyps."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.step_b_prop5.ensembles_hessenberg_p5c import (
        hessenberg_a_carre_egal_a_REEL,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import enonce_hessenberg
    res = hessenberg_a_carre_egal_a_REEL(E_set)

    cible = enonce_hessenberg(E_set)
    assert res.conclusion == cible, \
        f"hessenberg_a_carre_egal_a_0hyp : conclusion ≠ enonce_hessenberg\n{res.conclusion}"
    # ACCEPTANCE : exactement les 2 résidus honnêtes, E-niveau, conclusion ∉ hyps.
    H1, H2 = residu_H1(E_set), residu_H2(E_set)
    hyps = set(res.hypotheses)
    assert hyps == {H1, H2}, \
        "hessenberg_a_carre_egal_a_0hyp : hyps inattendues\n" + \
        "\n".join(str(h) for h in hyps)
    for h in res.hypotheses:
        assert set(libres_f(h)) <= {E_set}, \
            f"hessenberg_a_carre_egal_a_0hyp : hyp non E-niveau\n{h}"
    assert res.conclusion not in res.hypotheses, "hessenberg_a_carre_egal_a_0hyp : VACUOUS"
    return res


__all__ = [
    "residu_H1", "residu_H2", "residus_honnetes",
    "frame_a_maximal_clos", "hessenberg_a_carre_egal_a_0hyp",
]
