"""Tests §II.5.4 — Cor. 2 (sens utile) : un facteur vide annule le produit.

  ⊢ ( (α∈I) ∧ (X_α=∅) ) ⇒ ( ∏_{ι∈I} X_ι = ∅ ).

Vérifie la conclusion EXACTE (== cible reconstruite à la main), la clôture
(0 hypothèse) et l'invariant theorie_ensembles()==22.
"""
from bourbaki.logique.i_1_termes_relations.formule import (var, egal, et, impl, non, appartient)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_4_projection_partielle import (
    ensembles_produit_vide_ii5 as P)


def test_cor2_facteur_vide_donne_produit_vide_conclusion():
    thm = P.cor2_facteur_vide_donne_produit_vide("f", "I", "a", "F")
    vf, vI, va = var("f"), var("I"), var("a")
    X_a = E.valeur_famille(vf, va)
    produit = E.produit_famille(vf, vI)
    hyp = et(appartient(va, vI), egal(X_a, E.VIDE))
    cible = impl(hyp, egal(produit, E.VIDE))
    assert thm.conclusion == cible


def test_cor2_est_clos_et_zero_hypothese():
    thm = P.cor2_facteur_vide_donne_produit_vide()
    assert thm.est_clos
    assert len(thm.hypotheses) == 0


def test_cible_alias():
    assert P.cible is P.cor2_facteur_vide_donne_produit_vide


def test_theorie_ensembles_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
