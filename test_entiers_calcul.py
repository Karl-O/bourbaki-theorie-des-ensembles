"""Tests §III.5 — Calcul sur les entiers.

Vérifie : (1) les DÉFINITIONS de §III.5 se construisent (sans gonflement) ;
(2) l'axiome de l'intervalle d'entiers est bien formé (clos) ;
(3) les théorèmes DIRECTS (membre + 3 projections) == cible exacte + clos.

Tout le reste de §III.5 (Prop. 1-15, corollaires, division euclidienne,
développement de base b, combinatoire) repose sur la RÉCURRENCE (C61) et/ou
l'arithmétique cardinale binaire (NON disponibles) → REPORTÉ (cf. rapport &
docstrings de ensembles_entiers / ensembles_entiers_theoremes).
"""
from formule import var, egal, et, impl, equiv, appartient
import noyau_abrege as N
import ensembles_abrege as E
import ensembles_entiers as Ent
from ensembles_cardinaux import est_cardinal, inf_egal_card
from ensembles_entiers_theoremes import (
    axiome_intervalle_entiers,
    membre_intervalle_entiers,
    intervalle_implique_cardinal,
    intervalle_implique_borne_inf,
    intervalle_implique_borne_sup,
)


# ── (1) DÉFINITIONS §III.5 se construisent ────────────────────────────────────
def test_definitions_calcul_se_construisent():
    a, b, x = var("a"), var("b"), var("x")
    # §5.2 inégalité stricte + différence
    Ent.inf_strict_entiers(a, b)
    Ent.difference_entiers(b, a)
    # §5.3 intervalle + corps
    assert Ent.intervalle_entiers(a, b) == E.intervalle_entiers(a, b)
    Ent.corps_intervalle_entiers(a, b, x)
    # §5.4 suite finie + longueur
    Ent.est_suite_finie(var("t"), var("I"))
    Ent.longueur_suite(var("I"))
    # §5.5 fonction caractéristique
    Ent.fonction_caracteristique(var("A"), var("E"))
    # §5.6 pair/impair/divise/reste/quotient
    Ent.est_pair(a)
    Ent.est_impair(a)
    Ent.divise(b, a)
    Ent.reste_division(a, b)
    Ent.quotient_division(a, b)
    # §5.8 factorielle / binôme
    Ent.factorielle(var("n"))
    Ent.coefficient_binomial(var("n"), var("p"))


def test_pair_est_divise_par_deux():
    """est_pair(a) est, par définition, divise(2, a) (a multiple de 2, §5.6)."""
    a = var("a")
    assert Ent.est_pair(a) == Ent.divise(Ent.DEUX, a)


# ── (2) Axiome de l'intervalle bien formé ─────────────────────────────────────
def test_axiome_intervalle_bien_forme():
    ax = axiome_intervalle_entiers("a", "b", "x")
    # axiome clos (aucune variable libre)
    from formule import libres_f
    assert libres_f(ax) == set()
    # structure : (∀a)(∀b)(∀x)(...)
    assert ax.tag == "non"   # ∀ = ¬∃¬ au niveau primitif


# ── (3) THÉORÈMES DIRECTS §III.5.3 ────────────────────────────────────────────
def _cible_corps(a, b, x):
    return et(et(est_cardinal(x), inf_egal_card(a, x)), inf_egal_card(x, b))


def test_membre_intervalle_entiers():
    """⊢ (x∈[a,b]) ⇔ (x cardinal et a≤x et x≤b) — cible exacte + clos."""
    a, b, x = var("a"), var("b"), var("x")
    thm = membre_intervalle_entiers("a", "b", "x")
    cible = equiv(appartient(x, E.intervalle_entiers(a, b)), _cible_corps(a, b, x))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_intervalle_implique_cardinal():
    """⊢ (x∈[a,b]) ⇒ (x est un cardinal) — cible exacte + clos."""
    a, b, x = var("a"), var("b"), var("x")
    thm = intervalle_implique_cardinal("a", "b", "x")
    cible = impl(appartient(x, E.intervalle_entiers(a, b)), est_cardinal(x))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_intervalle_implique_borne_inf():
    """⊢ (x∈[a,b]) ⇒ (a ≤ x) — cible exacte + clos."""
    a, b, x = var("a"), var("b"), var("x")
    thm = intervalle_implique_borne_inf("a", "b", "x")
    cible = impl(appartient(x, E.intervalle_entiers(a, b)), inf_egal_card(a, x))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_intervalle_implique_borne_sup():
    """⊢ (x∈[a,b]) ⇒ (x ≤ b) — cible exacte + clos."""
    a, b, x = var("a"), var("b"), var("x")
    thm = intervalle_implique_borne_sup("a", "b", "x")
    cible = impl(appartient(x, E.intervalle_entiers(a, b)), inf_egal_card(x, b))
    assert thm.conclusion == cible
    assert thm.est_clos
