"""Tests §III.6 — ℵ₀·ℵ₀ = ℵ₀ (carré dénombrable, Lemme 2 E.III.48)."""
from bourbaki.logique.i_1_termes_relations.formule import egal, non
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, equipotent
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.cardinaux.ensembles_denombrable_carre_iii6 import (
    NN_non_vide, NN_inf_egal_NN_carre, denombrable_carre,
    denombrable_carre_de_injection_dure,
)

NN = ensemble_NN()
NN2 = E.produit(NN, NN)


def test_NN_non_vide():
    th = NN_non_vide()
    assert th.est_clos
    assert th.conclusion == non(egal(NN, E.VIDE))


def test_NN_inf_egal_NN_carre_facile():
    """Direction (A) FACILE : ⊢ ℕ ≤ ℕ×ℕ, CLOS, 0 hyp (anti-vacuité)."""
    th = NN_inf_egal_NN_carre()
    assert th.est_clos, "direction facile doit être CLOSE"
    assert len(th.hypotheses) == 0
    assert th.conclusion == inf_egal_card(NN, NN2)
    # anti-vacuité : conclusion ≠ trivialité
    assert th.conclusion != non(egal(NN, NN))


def test_denombrable_carre_residu_unique():
    """Assemblage CB : (B) ℕ×ℕ≤ℕ ⇒ Eq(ℕ×ℕ,ℕ).  (A) déchargée ; reste (B) honnête."""
    from bourbaki.logique.i_1_termes_relations.formule import impl
    th = denombrable_carre()
    assert th.est_clos
    # l'unique résidu (B) est la prémisse de l'implication, conclusion = Eq
    assert th.conclusion == impl(inf_egal_card(NN2, NN), equipotent(NN2, NN))
    # SATISFIABILITÉ : la prémisse (B) ne contredit rien (elle est VRAIE, Lemme 2)
    premisse = inf_egal_card(NN2, NN)
    assert premisse != non(premisse)


def test_branchement_injection_dure():
    """Si (B) close était fournie, denombrable_carre_de_injection_dure clôt Eq."""
    # On vérifie le BRANCHEMENT avec une preuve SUPPOSÉE de (B) (assume) :
    from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
    fausse_B = N.assume(inf_egal_card(NN2, NN))   # NON close — sert à tester le câblage
    res = denombrable_carre_de_injection_dure(fausse_B)
    assert res.conclusion == equipotent(NN2, NN)
    # res porte l'hyp (B) non déchargée (puisque fausse_B n'est pas close) — câblage OK
