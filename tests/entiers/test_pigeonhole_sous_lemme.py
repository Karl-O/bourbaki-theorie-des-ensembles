"""Tests du sous-lemme de la pigeonhole (Cor. 2 §III.4)."""
import bourbaki.ensembles.ensembles_abrege as E
from bourbaki.entiers.ensembles_pigeonhole_sous_lemme import (
    partie_egal_cardinal_egal, partie_egal_cardinal_egal_enonce,
    cor2_partie_propre_inf_strict, cor2_partie_propre_inf_strict_enonce,
)


def _nb_axiomes():
    th = E.theorie_ensembles()
    return len(th.axiomes) if hasattr(th, "axiomes") else len(list(th))


def test_partie_egal_cardinal_egal_clos():
    """⊢ (X⊂E et est_fini_ensemble(E) et Card X = Card E) ⇒ X = E : CLOS, 0 hyp."""
    r = partie_egal_cardinal_egal()
    assert r.est_clos
    assert not r.hypotheses


def test_partie_egal_cardinal_egal_conclusion():
    """Conclusion == énoncé attendu (pas de vacuité, conclusion ∉ hyps)."""
    r = partie_egal_cardinal_egal()
    assert r.conclusion == partie_egal_cardinal_egal_enonce()


def test_cor2_partie_propre_inf_strict_clos():
    """⊢ (X⊂E et ¬(X=E) et fini E) ⇒ Card X < Card E : CLOS, 0 hyp, conclusion == énoncé."""
    r = cor2_partie_propre_inf_strict()
    assert r.est_clos
    assert not r.hypotheses
    assert r.conclusion == cor2_partie_propre_inf_strict_enonce()


def test_theorie_inchangee():
    """Le noyau n'est pas touché : theorie_ensembles() = 22 axiomes."""
    partie_egal_cardinal_egal()
    assert _nb_axiomes() == 22
