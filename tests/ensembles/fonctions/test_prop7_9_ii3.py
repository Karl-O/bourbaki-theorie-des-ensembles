"""Tests §II.3 — Proposition 7 (réciproque fonction ⟺ injective) et
Proposition 9 (factorisation), module ensembles_prop7_9_ii3."""
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.fonctions.ii_3_general.ensembles_prop7_9_ii3 import (
    reciproque_fonctionnel_ssi_injectif, cible_reciproque_fonctionnel_ssi_injectif,
    reciproque_fonctionnel_implique_injectif, injectif_implique_reciproque_fonctionnel,
    prop9a_factorisation_valeur, cible_prop9a_factorisation_valeur,
    prop9b_factorisation_valeur, cible_prop9b_factorisation_valeur,
)


def test_theorie_intacte():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop7_equivalence_close():
    thm = reciproque_fonctionnel_ssi_injectif()
    assert thm.est_clos, thm.hypotheses
    assert thm.conclusion == cible_reciproque_fonctionnel_ssi_injectif()


def test_prop7_sens_necessaire():
    thm = reciproque_fonctionnel_implique_injectif()
    assert thm.est_clos


def test_prop7_sens_suffisant():
    thm = injectif_implique_reciproque_fonctionnel()
    assert thm.est_clos


def test_prop9a_factorisation():
    thm = prop9a_factorisation_valeur()
    assert thm.conclusion == cible_prop9a_factorisation_valeur()
    # honnête : conclusion non triviale (pas dans les hypothèses)
    assert thm.conclusion not in thm.hypotheses
    assert len(thm.hypotheses) >= 1


def test_prop9b_factorisation():
    thm = prop9b_factorisation_valeur()
    assert thm.conclusion == cible_prop9b_factorisation_valeur()
    assert thm.conclusion not in thm.hypotheses
