"""Tests §III.4 — Entiers naturels. Ensembles finis.

Vérifie : (1) les DÉFINITIONS se construisent (clos, sans gonflement) ;
(2) le théorème DIRECT « Card(X) est un cardinal » == cible exacte + clos.
"""
from formule import var, egal, et, non, impl
import noyau_abrege as N
import ensembles_entiers as Ent
from ensembles_cardinaux import cardinal, est_cardinal
from ensembles_entiers_theoremes import (
    card_est_un_cardinal,
    fini_implique_cardinal, fini_implique_distinct_successeur,
    caracterisation_fini, fini_implique_non_infini,
    ensemble_fini_card_est_cardinal, ensemble_fini_card_distinct_successeur)
import ensembles_infinis as Inf


def test_definitions_se_construisent():
    a = var("a")
    # Déf. 1
    f = Ent.est_fini(a)
    assert Ent.est_entier(a) == f          # entier naturel ≡ cardinal fini
    # successeur et premiers entiers
    assert Ent.UN == Ent.successeur(Ent.ZERO)
    assert Ent.DEUX == Ent.successeur(Ent.UN)
    # ensemble fini, famille finie
    Ent.est_fini_ensemble(var("E"))
    Ent.famille_finie(var("I"))
    # Déf. 2 caractère fini
    Ent.de_caractere_fini(var("S"), var("E"))


def test_card_est_un_cardinal():
    """⊢ Card(X) est un cardinal = ⊢ (∃X')(Card(X)=Card(X')) — cible exacte + clos."""
    thm = card_est_un_cardinal("X", "X'")
    cible = est_cardinal(cardinal(var("X")), "X'")
    assert thm.conclusion == cible
    assert thm.est_clos                    # clos (théorème, pas conditionnel)


def test_card_vide_est_un_cardinal():
    """0 = Card(∅) est un cardinal (cas particulier X := ∅, terme passé directement)."""
    import ensembles_abrege as E
    thm = card_est_un_cardinal(E.VIDE, "X'")
    cible = est_cardinal(cardinal(E.VIDE), "X'")
    assert thm.conclusion == cible
    assert thm.est_clos


# ── §III.4.1 — Déf. 1 (cardinal fini) dépliée : conjoints + caractérisation ────
def test_fini_implique_cardinal():
    """⊢ Fini(𝔞) ⇒ (𝔞 est un cardinal) — 1er conjoint de Déf. 1, cible exacte + clos."""
    a = var("a")
    thm = fini_implique_cardinal("a")
    assert thm.est_clos
    assert thm.conclusion == impl(Ent.est_fini(a), est_cardinal(a))


def test_fini_implique_distinct_successeur():
    """⊢ Fini(𝔞) ⇒ (𝔞 ≠ 𝔞 + 1) — 2e conjoint de Déf. 1, cible exacte + clos."""
    a = var("a")
    thm = fini_implique_distinct_successeur("a")
    assert thm.est_clos
    assert thm.conclusion == impl(Ent.est_fini(a), non(egal(a, Ent.successeur(a))))


def test_caracterisation_fini():
    """⊢ Fini(𝔞) ⇔ (𝔞 cardinal et 𝔞 ≠ 𝔞+1) — la Déf. 1 explicitée (A⇔A), clos."""
    a = var("a")
    thm = caracterisation_fini("a")
    assert thm.est_clos
    # Fini(𝔞) EST la conjonction ; l'équivalence est Fini(𝔞) ⇔ Fini(𝔞).
    from formule import equiv
    assert thm.conclusion == equiv(Ent.est_fini(a), Ent.est_fini(a))
    # et Fini(𝔞) est BIEN la conjonction (cardinal ∧ ≠succ)  — fidélité Déf. 1
    assert Ent.est_fini(a) == et(est_cardinal(a), non(egal(a, Ent.successeur(a))))


def test_fini_implique_non_infini():
    """⊢ Fini(𝔞) ⇒ ¬(𝔞 infini) — fini entraîne non infini, cible exacte + clos."""
    a = var("a")
    thm = fini_implique_non_infini("a")
    assert thm.est_clos
    assert thm.conclusion == impl(Ent.est_fini(a), non(Inf.est_infini(a)))


def test_ensemble_fini_card_est_cardinal():
    """⊢ (E fini) ⇒ (Card(E) cardinal) — Déf. 1 (ensemble fini), cible exacte + clos."""
    E_ = var("E")
    thm = ensemble_fini_card_est_cardinal("E")
    assert thm.est_clos
    assert thm.conclusion == impl(Ent.est_fini_ensemble(E_), est_cardinal(cardinal(E_)))


def test_ensemble_fini_card_distinct_successeur():
    """⊢ (E fini) ⇒ (Card(E) ≠ Card(E)+1) — Déf. 1 (ensemble fini), cible exacte + clos."""
    E_ = var("E")
    thm = ensemble_fini_card_distinct_successeur("E")
    assert thm.est_clos
    cible = impl(Ent.est_fini_ensemble(E_),
                 non(egal(cardinal(E_), Ent.successeur(cardinal(E_)))))
    assert thm.conclusion == cible
