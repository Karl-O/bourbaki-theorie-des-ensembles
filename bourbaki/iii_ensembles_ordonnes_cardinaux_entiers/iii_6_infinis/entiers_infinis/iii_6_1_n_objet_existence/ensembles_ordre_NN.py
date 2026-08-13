"""§III.6.1 / E.R.26 item 2 — ℕ EST ORDONNÉ PAR ≤ (n°63).

Bourbaki (Résumé E.R.26 item 2, def. E.III.1.1) : « N est ordonné par la relation
x ≤ y » (l'ordre des cardinaux restreint aux entiers).

FORMALISATION (relation, PAS graphe — évite la construction d'un graphe-ordre concret
qui exigerait un axiome S8 dédié, cf. journal tick 39).  La relation d'ordre SUR N est
la relation GARDÉE
        R_N(x, y) :=  x ∈ ℕ  et  y ∈ ℕ  et  x ≤ y            (≤ = inf_egal_card)
et l'énoncé-cible est le prédicat de Bourbaki `est_relation_ordre_dans(R_N, ℕ)` (E.III.1.1) :
        est_relation_ordre(R_N)  et  R_N réflexive dans ℕ,
soit TRANSITIVE ∧ ANTISYMÉTRIQUE ∧ (R{x,y}⇒R{x,x}∧R{y,y}) ∧ (∀x)(R{x,x} ⇔ x∈ℕ).

La garde « x∈ℕ et y∈ℕ » est REQUISE pour la fidélité : sans elle, ≤ (=inf_egal_card,
∃ injection) est réflexive sur TOUT ensemble (x≤x = identité) et son antisymétrie
échoue hors des cardinaux ; la garde confine l'ordre à ℕ, exactement le sens de
est_reflexive_dans_ordre (R{x,x} ⇔ x∈ℕ).

BRIQUES (toutes des lemmes DÉJÀ CLOS, pur assemblage) :
  · réflexivité de ≤     inf_egal_reflexif            (X≤X, inconditionnel) ;
  · transitivité de ≤    inf_egal_transitive_general  (∀-clos) ;
  · antisymétrie de ≤    inf_egal_antisymetrique_card (sur cardinaux) ;
  · x∈ℕ ⇒ Fini x         appartenance_NN_instanciee   (Th.1) ;
  · Fini x ⇒ cardinal x  fini_implique_cardinal.
theorie_ensembles() = 22 (ℕ existe déjà par le Théorème 1, sans axiome neuf).
⚠️ le test touche appartenance_NN ⇒ N_existe (~5 min, lru_cached) : test FICHIER SEUL.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, appartient, egal, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import (
    est_relation_ordre_dans)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import (
    ensemble_NN, appartenance_NN_instanciee)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import inf_egal_reflexif
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_props_restantes_ordre import (
    inf_egal_transitive_general, inf_egal_antisymetrique_card)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import fini_implique_cardinal


# ℕ = τy((∀x)(x∈y ⇔ Fini x))  — terme CLOS (Théorème 1).  Liants internes de NN : {x, y}
# ⇒ on quantifie l'énoncé sur n1, n2, n3 (≠ x, y) pour éviter toute collision.
NN = ensemble_NN()


def _RN(a, b):
    """R_N(a,b) := (a∈ℕ et b∈ℕ) et a≤b   (la relation d'ordre ≤ restreinte à ℕ)."""
    return et(et(appartient(a, NN), appartient(b, NN)), inf_egal_card(a, b))


def _cardinal_de_NN(preuve_in, t):
    """De ⊢{Γ} t∈ℕ, déduire ⊢{Γ} est_cardinal(t)  (t∈ℕ ⇒ Fini t ⇒ cardinal t)."""
    fini_t = N.modus_ponens(preuve_in, equivalence_avant(appartenance_NN_instanciee(t)))
    return N.modus_ponens(fini_t, fini_implique_cardinal(t))


def enonce_ordre_NN(x="n1", y="n2", z="n3"):
    return est_relation_ordre_dans(_RN, NN, x, y, z)


# ── composante 1 : TRANSITIVITÉ de R_N ────────────────────────────────────────
def _transitif():
    n1, n2, n3 = var("n1"), var("n2"), var("n3")
    ante = et(_RN(n1, n2), _RN(n2, n3))
    h = N.assume(ante)
    h12, h23 = conjonction_elim_gauche(h), conjonction_elim_droite(h)
    n1_in = conjonction_elim_gauche(conjonction_elim_gauche(h12))     # n1∈ℕ
    n3_in = conjonction_elim_droite(conjonction_elim_gauche(h23))     # n3∈ℕ
    le12 = conjonction_elim_droite(h12)                              # n1≤n2
    le23 = conjonction_elim_droite(h23)                              # n2≤n3
    trans = instancie(instancie(instancie(inf_egal_transitive_general(), n1), n2), n3)
    le13 = N.modus_ponens(conjonction_intro(le12, le23), trans)       # n1≤n3
    concl = conjonction_intro(conjonction_intro(n1_in, n3_in), le13)  # R_N(n1,n3)
    body = N.loi_deduction(ante, concl)
    return N.generalisation("n1", N.generalisation("n2", N.generalisation("n3", body)))


# ── composante 2 : ANTISYMÉTRIE de R_N ────────────────────────────────────────
def _antisymetrique():
    n1, n2 = var("n1"), var("n2")
    ante = et(_RN(n1, n2), _RN(n2, n1))
    h = N.assume(ante)
    h12, h21 = conjonction_elim_gauche(h), conjonction_elim_droite(h)
    n1_in = conjonction_elim_gauche(conjonction_elim_gauche(h12))     # n1∈ℕ
    n2_in = conjonction_elim_droite(conjonction_elim_gauche(h12))     # n2∈ℕ
    le12 = conjonction_elim_droite(h12)                              # n1≤n2
    le21 = conjonction_elim_droite(h21)                              # n2≤n1
    card1 = _cardinal_de_NN(n1_in, n1)
    card2 = _cardinal_de_NN(n2_in, n2)
    antisym = instancie(instancie(inf_egal_antisymetrique_card(), n1), n2)
    premisse = conjonction_intro(conjonction_intro(conjonction_intro(le12, le21), card1), card2)
    eq12 = N.modus_ponens(premisse, antisym)                         # n1=n2
    body = N.loi_deduction(ante, eq12)
    return N.generalisation("n1", N.generalisation("n2", body))


# ── composante 3 : R{x,y} ⇒ (R{x,x} et R{y,y}) ────────────────────────────────
def _reflexif_implicite():
    n1, n2 = var("n1"), var("n2")
    h = N.assume(_RN(n1, n2))
    n1_in = conjonction_elim_gauche(conjonction_elim_gauche(h))       # n1∈ℕ
    n2_in = conjonction_elim_droite(conjonction_elim_gauche(h))       # n2∈ℕ
    RN11 = conjonction_intro(conjonction_intro(n1_in, n1_in), inf_egal_reflexif("n1"))
    RN22 = conjonction_intro(conjonction_intro(n2_in, n2_in), inf_egal_reflexif("n2"))
    body = N.loi_deduction(_RN(n1, n2), conjonction_intro(RN11, RN22))
    return N.generalisation("n1", N.generalisation("n2", body))


# ── composante 4 : R_N RÉFLEXIVE DANS ℕ  ((∀x)(R{x,x} ⇔ x∈ℕ)) ─────────────────
def _reflexive_dans():
    n1 = var("n1")
    A = _RN(n1, n1)                       # et(et(n1∈ℕ,n1∈ℕ), n1≤n1)
    B = appartient(n1, NN)                # n1∈ℕ
    imp_AB = N.loi_deduction(A, conjonction_elim_gauche(conjonction_elim_gauche(N.assume(A))))
    hB = N.assume(B)
    A_built = conjonction_intro(conjonction_intro(hB, hB), inf_egal_reflexif("n1"))
    imp_BA = N.loi_deduction(B, A_built)
    return N.generalisation("n1", conjonction_intro(imp_AB, imp_BA))


# @livre Ch.R §6 Demo.- | E.R.26 item 2 | PDF p.329   (ℕ est ordonné par ≤)
def ordre_NN():
    """🎯 ⊢ est_relation_ordre_dans(R_N, ℕ)  —  ℕ EST ORDONNÉ PAR ≤ (n°63).  CLOS, 0 hyp.

    est_relation_ordre_dans = et( et( et(transitif, antisym), reflexif_implicite),
    reflexive_dans ) — assemblage des 4 composantes."""
    res = conjonction_intro(
        conjonction_intro(conjonction_intro(_transitif(), _antisymetrique()),
                          _reflexif_implicite()),
        _reflexive_dans())
    assert res.conclusion == enonce_ordre_NN(), "ordre_NN : conclusion ≠ énoncé attendu"
    return res


__all__ = ["enonce_ordre_NN", "ordre_NN"]
