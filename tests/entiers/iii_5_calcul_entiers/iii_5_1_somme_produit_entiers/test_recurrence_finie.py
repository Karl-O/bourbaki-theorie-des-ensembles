"""Tests — PRINCIPE DE RÉCURRENCE SUR LES ENSEMBLES FINIS (recurrence_finie)."""
from bourbaki.logique.i_1_termes_relations.formule import var, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_recurrence_finie import (
    recurrence_finie, recurrence_finie_enonce, _preuve_Q0, _preuve_step,
    _pas_ensemble, _Q,
)
import bourbaki.logique.i_2_criteres_C.noyau.noyau_abrege as N


# prédicat de test arbitraire P(t) := t ∈ a
def _P(t):
    return appartient(t, var("a"))


def test_Q0_sous_P_vide():
    hP0 = N.assume(_P(E.VIDE))
    q0 = _preuve_Q0(_P, hP0)
    assert q0.conclusion == _Q(_P, "XQ")(__import__(
        "bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers", fromlist=["ZERO"]).ZERO)


def test_step_sous_pas():
    hPas = N.assume(_pas_ensemble(_P, "Xrec", "xrec"))
    step = _preuve_step(_P, hPas)
    # le pas est l'UNIQUE hypothèse
    assert len(step.hypotheses) == 1


def test_recurrence_finie_close():
    res = recurrence_finie(_P)
    assert res.est_clos, "recurrence_finie doit être CLOS (0 hypothèse)"
    assert len(res.hypotheses) == 0
    assert res.conclusion == recurrence_finie_enonce(_P)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22
