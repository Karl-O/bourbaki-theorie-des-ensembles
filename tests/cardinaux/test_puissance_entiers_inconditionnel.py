"""Acceptance — a^b ∈ ℕ INCONDITIONNEL (Cor. 3 §III.5.1, B0/B déchargés)."""
from bourbaki.logique.formule import var, impl, et
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.cardinaux.ensembles_n_arith_iii5 import (
    exposant_invariance_zero_enonce, exposant_invariance_enonce,
)
from bourbaki.cardinaux.ensembles_puissance_entiers_inconditionnel import (
    B0_preuve, B_preuve, puissance_entiers_ferme_inconditionnel,
)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles


def test_B0_decharge():
    b0 = B0_preuve()
    assert b0.est_clos
    assert not list(b0.hypotheses)
    assert b0.conclusion == exposant_invariance_zero_enonce(var("apuf"))


def test_B_decharge():
    bn = B_preuve()
    assert bn.est_clos
    assert not list(bn.hypotheses)
    assert bn.conclusion == exposant_invariance_enonce(var("apuf"), var("npuf"))


def test_puissance_entiers_ferme_inconditionnel_clean_target():
    thm = puissance_entiers_ferme_inconditionnel()
    a, b = var("apuf"), var("bpuf")
    target = impl(et(est_fini(a), est_fini(b)),
                  est_fini(exposant_cardinal_binaire(a, b)))
    assert thm.est_clos
    assert not list(thm.hypotheses)
    # CLEAN target: NO B0/B antecedents folded in
    assert thm.conclusion == target


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
