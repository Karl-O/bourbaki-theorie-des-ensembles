"""Tests §III.3.2 — PROPOSITION 2 (forme ENSEMBLISTE) : existence de la BORNE
SUPÉRIEURE d'un ensemble de cardinaux majoré.   Via le BON ORDRE des cardinaux ≤ a
(`cardinaux_bien_ordonnes_close`, CLOS) + COMPARABILITÉ (CLOSE).   theorie=22.

⚠️ Le test principal `test_borne_superieure_existe` est COÛTEUX (~5 min : bon ordre).
Les autres tests (formes, lemmes cheap, théorie) sont rapides.
"""
import pytest

from bourbaki.logique.i_1_termes_relations.formule import (var, app, egal, et, impl, equiv, pourtout,
                                       appartient, non, inclus)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, inf_egal_card
from bourbaki.cardinaux import ensembles_sup_cardinal as SUP


# ── notions (formes) ──────────────────────────────────────────────────────────
def test_majore_clause_forme():
    vF, vm, vc = var("Fsup"), var("m"), var("cmaj")
    assert SUP.majore_clause(vF, vm) == \
        pourtout("cmaj", impl(appartient(vc, vF), inf_egal_card(vc, vm)))


def test_ensemble_majorants_terme():
    vF, va = var("Fsup"), var("a")
    assert SUP.ensemble_majorants(vF, va) == app("majorants_card", vF, va)


def test_relation_majorant_forme():
    vF, va, vm = var("Fsup"), var("a"), var("m")
    assert SUP.relation_majorant(vF, va, vm) == \
        et(appartient(vm, SUP.intervalle_0a("a")), SUP.majore_clause(vF, vm))


def test_membre_majorants_forme():
    vF, va, vm = var("Fsup"), var("a"), var("m")
    thm = SUP.membre_majorants(vF, va, vm)
    assert thm.est_clos
    assert thm.conclusion == equiv(appartient(vm, SUP.ensemble_majorants(vF, va)),
                                   SUP.relation_majorant(vF, va, vm))


def test_est_borne_superieure_ensemble_forme():
    vs, vF = var("s"), var("Fsup")
    out = SUP.est_borne_superieure_ensemble(vs, vF)
    assert out == et(et(est_cardinal(vs), SUP.majore_famille_ensemble(vs, vF)),
                     SUP.plus_petit_majorant_ensemble(vs, vF))


# ── lemmes cheap clos / honnêtes ──────────────────────────────────────────────
def test_majorants_inclus_interv_close():
    """⊢ U ⊂ [0,a]   CLOS (0 hyp)."""
    thm = SUP.majorants_inclus_interv("Fsup", "a")
    assert thm.est_clos
    U = SUP.ensemble_majorants(var("Fsup"), var("a"))
    assert thm.conclusion == inclus(U, SUP.intervalle_0a("a"), z="z")


def test_a_dans_majorants_hyps():
    """⊢ { est_cardinal(a), F⊂[0,a] } ⊢ a∈U."""
    thm = SUP.a_dans_majorants("Fsup", "a")
    U = SUP.ensemble_majorants(var("Fsup"), var("a"))
    assert thm.conclusion == appartient(var("a"), U)
    expected = {est_cardinal(var("a")), inclus(var("Fsup"), SUP.intervalle_0a("a"))}
    assert thm.hypotheses == expected


def test_majorants_non_vide_hyps():
    """⊢ { est_cardinal(a), F⊂[0,a] } ⊢ ¬(U=∅)."""
    thm = SUP.majorants_non_vide("Fsup", "a")
    U = SUP.ensemble_majorants(var("Fsup"), var("a"))
    assert thm.conclusion == non(egal(U, E.VIDE))
    expected = {est_cardinal(var("a")), inclus(var("Fsup"), SUP.intervalle_0a("a"))}
    assert thm.hypotheses == expected


def test_comparabilite_cardinaux_terme_close():
    """⊢ (c≤a) OU (a≤c)   CLOS (comparabilité, INCONDITIONNEL via Zorn)."""
    from bourbaki.logique.i_1_termes_relations.formule import ou
    thm = SUP.comparabilite_cardinaux_terme(var("c"), var("a"))
    assert thm.est_clos
    assert thm.conclusion == ou(inf_egal_card(var("c"), var("a")),
                                inf_egal_card(var("a"), var("c")))


# ── garde-fous théorie / noyau ────────────────────────────────────────────────
def test_theorie_22():
    """theorie_ensembles() reste à 22 (la théorie DÉDIÉE des majorants est SÉPARÉE)."""
    assert len(E.theorie_ensembles().axiomes) == 22
    # la théorie dédiée ne contient QUE son axiome (séparée)
    assert len(SUP.theorie_majorants_F().axiomes) == 1


# ── LE THÉORÈME (COÛTEUX) ─────────────────────────────────────────────────────
@pytest.mark.slow
def test_borne_superieure_existe():
    """🎯🎯 PROP 2 (ensembliste) : ⊢ { est_cardinal(a), F⊂[0,a] } ⊢
        (∃s) est_borne_superieure_ensemble(s, F, a).

    HYPOTHÈSES exactement {est_cardinal(a), F⊂[0,a]} (honnêtes, intendues) ; F≠∅
    SUPERFLU.  Conclusion == cible déposée.  theorie=22."""
    thm = SUP.borne_superieure_existe("Fsup", "a")
    expected = {est_cardinal(var("a")),
                inclus(var("Fsup"), SUP.intervalle_0a("a"))}
    assert thm.hypotheses == expected, \
        f"hyps inattendues: {thm.hypotheses}"
    assert thm.conclusion == SUP.borne_superieure_existe_cible("Fsup", "a")
    assert len(E.theorie_ensembles().axiomes) == 22
