"""Tests — §III.5 Cor.3 puissance d'entiers (ensembles_n_arith_iii5).

G2 `puissance_entiers_ferme` ⊢ (B0 et (∀m)B) ⇒ ((Fini a et Fini b) ⇒ Fini(a^b)),
certifié sous les SEULES hypothèses de support (exponent-invariance), via le maillon
a^(n+1)=a^n·a (puissance_succ_eq) + G1 (produit_binaire_entier) + récurrence C61.
theorie=22, kernel intact.
"""
from bourbaki.logique.formule import var, egal, et, impl, pourtout
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini, successeur, ZERO
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.cardinaux.ensembles_n_arith_iii5 import (
    exposant_invariance_enonce, exposant_invariance_zero_enonce,
    puissance_succ_eq, puissance_entiers_ferme,
)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_maillon_puissance_succ_eq():
    """⊢ B(a,n) ⇒ ((card a et card n) ⇒ a^(n+1)=a^n·a).  Clos, 0 hyp."""
    m = puissance_succ_eq()
    assert m.est_clos
    assert len(m.hypotheses) == 0
    va, vn = var("Apse"), var("Npse")
    an = exposant_cardinal_binaire(va, vn)
    lhs = exposant_cardinal_binaire(va, successeur(vn))
    rhs = produit_cardinal_binaire(an, va)
    cible = impl(exposant_invariance_enonce(va, vn),
                 impl(et(est_cardinal(va), est_cardinal(vn)), egal(lhs, rhs)))
    assert m.conclusion == cible


def test_g2_puissance_entiers_ferme():
    """🎯 G2 : (B0 et (∀m)B) ⇒ ((Fini a et Fini b) ⇒ Fini(a^b)).  Clos, 0 hyp."""
    g2 = puissance_entiers_ferme()
    assert g2.est_clos
    assert len(g2.hypotheses) == 0
    va, vb = var("apuf"), var("bpuf")
    B0 = exposant_invariance_zero_enonce(va)
    Buniv = pourtout("mPpu", exposant_invariance_enonce(va, "mPpu"))
    cible = impl(B0, impl(Buniv,
                impl(et(est_fini(va), est_fini(vb)),
                     est_fini(exposant_cardinal_binaire(va, vb)))))
    assert g2.conclusion == cible
    # anti-vacuité : conclusion ≠ hypothèses ; les deux côtés de B sont distincts
    B = exposant_invariance_enonce(va, vb)
    assert B.termes[0] != B.termes[1]
    assert B0 != B
