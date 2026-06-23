"""Tests — DIRECTION B (ψ) et CLÔTURE INCONDITIONNELLE de la Proposition 9.

§III.3.5 : a^(b+c) = a^b·a^c, c.-à-d. Card(𝓕(B⊔C;A)) = Card(𝓕(B;A)×𝓕(C;A)).
Le dernier pas : ψ-injectivité ⇒ inf_egal_psi ⇒ prop9_close (Cantor–Bernstein)."""
from bourbaki.logique.formule import var, appartient, egal
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.arithmetique.ensembles_prop9_exp_somme import (
    cible_prop9_exp_somme)
from bourbaki.cardinaux.arithmetique.ensembles_prop9_close import (
    codomaine_phi, psi_valeur)
from bourbaki.cardinaux.arithmetique import ensembles_prop9_final_close as M


def test_W_psi_valeur():
    # W_ψ(p) = ψ(p)  sous l'unique hypothèse p ∈ cod (comme W_phi_valeur).
    th = M.W_psi_valeur("q", "A", "B", "C")
    cod = codomaine_phi(var("A"), var("B"), var("C"))
    assert th.hypotheses == frozenset({appartient(var("q"), cod)}), \
        ("W_psi_valeur : hypothèses inattendues : " + repr(th.hypotheses))
    expected = egal(E.valeur(M.W_psi(var("A"), var("B"), var("C")), var("q")),
                    psi_valeur(var("q"), var("A"), var("B"), var("C")))
    assert th.conclusion == expected, "W_psi_valeur : conclusion != W_ψ(q)=ψ(q)"


def test_W_psi_injective_clos():
    th = M.W_psi_injective("A", "B", "C")
    assert th.est_clos, ("W_psi_injective non clos : " + repr(th.hypotheses))


def test_W_psi_est_injection_clos():
    th = M.W_psi_est_injection("A", "B", "C")
    assert th.est_clos, ("W_psi_est_injection non clos : " + repr(th.hypotheses))


def test_inf_egal_psi_clos():
    th = M.inf_egal_psi("A", "B", "C")
    assert th.est_clos, ("inf_egal_psi non clos : " + repr(th.hypotheses))


def test_prop9_close_inconditionnel():
    th = M.prop9_close("A", "B", "C")
    assert th.est_clos, ("prop9_close NON clos : " + repr(th.hypotheses))
    assert th.conclusion == cible_prop9_exp_somme(var("A"), var("B"), var("C")), \
        "prop9_close.conclusion != cible_prop9_exp_somme"


def test_theorie_intacte_22_axiomes():
    assert len(E.theorie_ensembles().axiomes) == 22, "theorie_ensembles != 22 axiomes"
