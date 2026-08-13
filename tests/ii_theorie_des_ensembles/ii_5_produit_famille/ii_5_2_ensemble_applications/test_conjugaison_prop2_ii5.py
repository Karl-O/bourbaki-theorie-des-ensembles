"""Tests §II.5 — Proposition 2 (E II.31), cas 1° injectif (forme rétraction/section)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_ensemble_applications.ensembles_conjugaison_prop2_ii5 import (
    prop2_conjugaison_injective, cible_prop2_conjugaison_injective)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop2_conjugaison_injective_close():
    """Résultat CLOS : 0 hypothèse non déchargée (implication curryfiée)."""
    th = prop2_conjugaison_injective()
    assert th.est_clos
    assert len(th.hypotheses) == 0


def test_prop2_conclusion_exacte():
    """La conclusion est LITTÉRALEMENT (H₀ ⇒ … ⇒ H₁₁ ⇒ (f₁ = f₂)) : sous les 12
    hypothèses rétraction/section, deux applications de même conjuguée v∘f∘u sont
    égales — l'énoncé extensionnel du cas injectif de la Proposition 2 (E II.31)."""
    th = prop2_conjugaison_injective()
    assert th.conclusion == cible_prop2_conjugaison_injective()
    # theorie inchangée APRÈS construction
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop2_noms_libres_parametrables():
    """Le résultat se re-paramètre (noms de variables libres arbitraires)."""
    th = prop2_conjugaison_injective("g1", "g2", "u0", "v0", "s0", "r0",
                                     "A", "Ap", "B")
    assert th.est_clos
    assert th.conclusion == cible_prop2_conjugaison_injective(
        "g1", "g2", "u0", "v0", "s0", "r0", "A", "Ap", "B")
    # le membre final est bien g1 = g2
    concl = th.conclusion
    while concl.tag == "ou":            # dérouler les implications (impl = ou(non·,·))
        concl = concl.sous[1]
    assert concl == egal(var("g1"), var("g2"))
