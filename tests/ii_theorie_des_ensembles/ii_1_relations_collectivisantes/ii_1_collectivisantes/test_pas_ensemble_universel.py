"""Tests — E.II.6, Remarque : ⊢ ¬(∃X)(∀x)(x ∈ X) (pas d'ensemble universel)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, non, appartient, existe, pourtout, tau,
                     libres_f)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ii_1_collectivisantes.ensembles_pas_ensemble_universel import (
    pas_ensemble_universel)


def _cible():
    return non(existe("X", pourtout("x", appartient(var("x"), var("X")))))


def _contient_tau_f(f):
    return any(_contient_tau_t(t) for t in f.termes) or any(_contient_tau_f(s) for s in f.sous)


def _contient_tau_t(t):
    return t.tag == "tau" or any(_contient_tau_t(a) for a in t.args)


def test_pas_ensemble_universel_conclusion():
    # ⊢ ¬(∃X)(∀x)(x ∈ X) : conclusion == cible (égalité STRUCTURELLE).
    t = pas_ensemble_universel()
    assert t.conclusion == _cible()


def test_pas_ensemble_universel_clos():
    # Théorème CLOS : zéro hypothèse non déchargée (témoin X0 / sélection R0 éliminés).
    t = pas_ensemble_universel()
    assert t.est_clos
    assert t.hypotheses == frozenset()


def test_pas_ensemble_universel_aucun_tau():
    # AUCUN τ résiduel dans la conclusion : c'est bien l'énoncé du livre (X0 éliminé).
    t = pas_ensemble_universel()
    assert not _contient_tau_f(t.conclusion)
    assert libres_f(t.conclusion) == set()


def test_theorie_reste_22_axiomes():
    # Invariant projet : la sélection S8 de R0 vit dans une théorie DÉDIÉE.
    assert len(E.theorie_ensembles().axiomes) == 22


def test_temoin_universel_elimine():
    # Le terme-témoin X0 = τX(…) est bien un τ-terme, mais il a été ÉLIMINÉ de la
    # conclusion close (décharge de H) : la conclusion ne le contient pas.
    t = pas_ensemble_universel()
    X0 = tau("X", pourtout("x", appartient(var("x"), var("X"))))
    assert _contient_tau_t(X0)                # X0 est bien un τ-terme
    assert not _contient_tau_f(t.conclusion)  # … absent de la conclusion
