"""Tests — §III.4 : CORRESPONDANCE ORDINAL↔CARDINAL → cardinaux_bien_ordonnes(a).

Vérifie le SALVAGE FORT GRADUÉ du bottleneck #1 (vers ℕ inconditionnel) :

  ✅ INCONDITIONNEL :
     • ENGINE plus_petit_de_bon_ordre (extraction du plus petit élément d'un bon ordre).
     • RÉDUCTION cardinaux_bien_ordonnes_de_bon_ordre : la cible est == clause_plus_petit(≤,[0,a]).
     • PARTIE ORDRE complète : est_relation_ordre_dans(≤_induit,[0,a]) CLOS
       (transitivité, ANTISYMÉTRIE Cantor–Bernstein, réflexivité-implicite, réflexivité-dans-E).
  ⊢ FINAL : cardinaux_bien_ordonnes(a) DÉRIVÉ de l'UNIQUE report clause_plus_petit.

theorie_ensembles() = 22 partout, conclusions == cibles Bourbaki LITTÉRALEMENT.
"""
from bourbaki.logique.formule import var, appartient, et, non, egal, existe, pourtout, inclus
from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege2 import conjonction_intro
import bourbaki.logique.noyau_abrege as N

from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import cardinaux_bien_ordonnes

from bourbaki.cardinaux.ensembles_ordinal_cardinal_bon_ordre import (
    clause_plus_petit, bon_ordre_donne_clause_plus_petit, plus_petit_de_bon_ordre,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal_correspondance import (
    intervalle_0a, ordre_induit_intervalle, bon_ordre_intervalle,
    plus_petit_induit_donne_bare, clause_induite_donne_bare,
    cardinaux_bien_ordonnes_de_bon_ordre,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal_ordre import (
    reflexive_dans_intervalle, reflexif_implicite_intervalle,
    transitif_intervalle, antisymetrie_intervalle, relation_ordre_dans_intervalle,
)
from bourbaki.cardinaux.ensembles_ordinal_cardinal import (
    report_clause_plus_petit, cardinaux_bien_ordonnes_de_clause,
)


def _graphe_R(G):
    vG = var(G)
    return lambda a, b: appartient(E.couple(
        a if hasattr(a, "nom") else var(a), b if hasattr(b, "nom") else var(b)), vG)


# ════════════════════════════════════════════════════════════════════════════
#  THEORIE = 22 (invariant global)
# ════════════════════════════════════════════════════════════════════════════
def test_theorie_ensembles_22():
    assert len(E.theorie_ensembles().axiomes) == 22


# ════════════════════════════════════════════════════════════════════════════
#  ENGINE — extraction du plus petit élément d'un bon ordre (INCONDITIONNEL)
# ════════════════════════════════════════════════════════════════════════════
def test_bon_ordre_donne_clause_plus_petit_clos():
    """⊢ est_bien_ordonne(R,E) ⇒ clause_plus_petit(R,E)   CLOS (projection Déf.1)."""
    R = _graphe_R("G")
    th = bon_ordre_donne_clause_plus_petit(R, "E")
    assert th.est_clos
    # le conséquent est EXACTEMENT clause_plus_petit(R,E)
    assert th.conclusion.sous[1] == clause_plus_petit(R, "E")


def test_plus_petit_de_bon_ordre_hyps():
    """ENGINE : { est_bien_ordonne(R,E), X⊂E, X≠∅ } ⊢ (∃a)(a∈X et (∀w)(w∈X⇒R{a,w}))."""
    R = _graphe_R("G")
    th = plus_petit_de_bon_ordre(R, "E", "X")
    # exactement 3 hypothèses : bon ordre, inclusion, non-vacuité
    assert len(th.hypotheses) == 3
    ve, vX = var("E"), var("X")
    assert E.est_bien_ordonne(R, ve) in th.hypotheses
    assert inclus(vX, ve) in th.hypotheses
    assert non(egal(vX, E.VIDE)) in th.hypotheses


# ════════════════════════════════════════════════════════════════════════════
#  RÉDUCTION — la cible EST la clause de plus petit élément sur [0,a]
# ════════════════════════════════════════════════════════════════════════════
def test_cible_est_clause_plus_petit_bare():
    """cardinaux_bien_ordonnes(a) == clause_plus_petit(≤, [0,a])  (DÉCOUVERTE clé)."""
    Rle = lambda u, v: inf_egal_card(
        u if hasattr(u, "nom") else var(u), v if hasattr(v, "nom") else var(v))
    cible = cardinaux_bien_ordonnes("a", "S", "m", "x")
    clause = clause_plus_petit(Rle, intervalle_0a("a"), X="S", a="m", w="x")
    assert cible == clause


def test_plus_petit_induit_donne_bare_clos():
    """⊢ (m∈S et (∀x)(x∈S⇒R_induit{m,x})) ⇒ (m∈S et (∀x)(x∈S⇒m≤x))  CLOS."""
    th = plus_petit_induit_donne_bare("a")
    assert th.est_clos


def test_clause_induite_donne_bare_clos():
    """⊢ (∃m)…R_induit ⇒ (∃m)…bare   CLOS (monotonie du ∃m, projection induit→bare)."""
    th = clause_induite_donne_bare("a")
    assert th.est_clos


def test_cardinaux_bien_ordonnes_de_bon_ordre():
    """{ est_bien_ordonne(≤_induit,[0,a]) } ⊢ cardinaux_bien_ordonnes(a)  (conclusion == cible)."""
    th = cardinaux_bien_ordonnes_de_bon_ordre("a", "S", "m", "x")
    assert th.conclusion == cardinaux_bien_ordonnes("a", "S", "m", "x")
    # UNIQUE hypothèse = le bon ordre de [0,a]
    assert list(th.hypotheses) == [bon_ordre_intervalle("a")]


# ════════════════════════════════════════════════════════════════════════════
#  PARTIE ORDRE — les 4 paliers (INCONDITIONNELS, == leurs prédicats)
# ════════════════════════════════════════════════════════════════════════════
def test_reflexive_dans_intervalle():
    """⊢ est_reflexive_dans_ordre(≤_induit,[0,a])  CLOS == le prédicat."""
    th = reflexive_dans_intervalle("a")
    Rind, interv = ordre_induit_intervalle("a"), intervalle_0a("a")
    assert th.est_clos
    assert th.conclusion == E.est_reflexive_dans_ordre(Rind, interv, "x")


def test_reflexif_implicite_intervalle():
    """⊢ ordre_reflexif_implicite(≤_induit)  CLOS == le prédicat."""
    th = reflexif_implicite_intervalle("a")
    Rind = ordre_induit_intervalle("a")
    assert th.est_clos
    assert th.conclusion == E.ordre_reflexif_implicite(Rind, "xo", "yo")


def test_transitif_intervalle():
    """⊢ ordre_transitif(≤_induit)  CLOS == le prédicat (via inf_egal_transitive)."""
    th = transitif_intervalle("a")
    Rind = ordre_induit_intervalle("a")
    assert th.est_clos
    assert th.conclusion == E.ordre_transitif(Rind, "xo", "yo", "zo")


def test_antisymetrie_intervalle():
    """⊢ ordre_antisymetrique(≤_induit)  CLOS == le prédicat (CANTOR–BERNSTEIN)."""
    th = antisymetrie_intervalle("a")
    Rind = ordre_induit_intervalle("a")
    assert th.est_clos
    assert th.conclusion == E.ordre_antisymetrique(Rind, "xo", "yo")


def test_relation_ordre_dans_intervalle():
    """🎯 ⊢ est_relation_ordre_dans(≤_induit,[0,a])  CLOS == le prédicat (4 paliers assemblés)."""
    th = relation_ordre_dans_intervalle("a")
    Rind, interv = ordre_induit_intervalle("a"), intervalle_0a("a")
    assert th.est_clos
    assert th.conclusion == E.est_relation_ordre_dans(Rind, interv, "xo", "yo", "zo")


# ════════════════════════════════════════════════════════════════════════════
#  ASSEMBLAGE FINAL — cible DÉRIVÉE de l'UNIQUE report clause_plus_petit
# ════════════════════════════════════════════════════════════════════════════
def test_cardinaux_bien_ordonnes_de_clause():
    """🎯🎯 { clause_plus_petit(≤_induit,[0,a]) } ⊢ cardinaux_bien_ordonnes(a).

    Conclusion == la cible LITTÉRALEMENT ; UNIQUE hypothèse résiduelle == le report
    clause_plus_petit (la partie ORDRE de est_bien_ordonne étant PROUVÉE)."""
    th = cardinaux_bien_ordonnes_de_clause("a", "S", "m", "x")
    assert th.conclusion == cardinaux_bien_ordonnes("a", "S", "m", "x")
    assert list(th.hypotheses) == [report_clause_plus_petit("a")]
