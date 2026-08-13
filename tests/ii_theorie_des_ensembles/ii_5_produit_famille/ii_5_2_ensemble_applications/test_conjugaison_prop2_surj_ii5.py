"""Tests §II.5 — Proposition 2 (E II.31), cas 2° surjectif (forme rétraction/section)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, existe
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_2_ensemble_applications.ensembles_conjugaison_prop2_surj_ii5 import (
    prop2_conjugaison_surjective, cible_prop2_conjugaison_surjective)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop2_conjugaison_surjective_close():
    """Résultat CLOS : 0 hypothèse non déchargée (implication curryfiée)."""
    th = prop2_conjugaison_surjective()
    assert th.est_clos
    assert len(th.hypotheses) == 0


def test_prop2_surj_conclusion_exacte():
    """La conclusion est (H₀ ⇒ … ⇒ H₅ ⇒ (∃f)(f:E→F ∧ v∘f∘u = g)) : sous les 6
    hypothèses rétraction/section, tout g admet un antécédent — la surjectivité
    du cas 2° de la Proposition 2 (E II.31)."""
    th = prop2_conjugaison_surjective()
    assert th.conclusion == cible_prop2_conjugaison_surjective()
    assert len(E.theorie_ensembles().axiomes) == 22


def test_prop2_surj_membre_final_est_existentielle():
    """Après avoir déroulé les 6 implications, le membre final est un ∃f (existence
    d'un antécédent) — l'énoncé de surjectivité."""
    concl = prop2_conjugaison_surjective().conclusion
    while concl.tag == "ou":            # impl = ou(non·, ·)
        concl = concl.sous[1]
    assert concl.tag == "exists"
    assert concl.lieur == "f"


def test_prop2_surj_noms_libres_parametrables():
    th = prop2_conjugaison_surjective("g0", "u0", "r0", "s0", "v0",
                                      "A", "Ap", "B", "Bp")
    assert th.est_clos
    assert th.conclusion == cible_prop2_conjugaison_surjective(
        "g0", "u0", "r0", "s0", "v0", "A", "Ap", "B", "Bp")
