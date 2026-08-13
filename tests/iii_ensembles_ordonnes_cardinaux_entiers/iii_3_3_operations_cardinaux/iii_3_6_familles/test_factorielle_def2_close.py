# -*- coding: utf-8 -*-
"""Test §III.5.8 Déf.2 — la récursion DÉCHARGÉE (H2/H3 coupées).  theorie==22.

⚠️ LENT : T1b-1 déclenche N_existe (~5 min, mémoïsé/session)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_factorielle_def2_close import (
    factorielle_def2_dechargee,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_factorielle_def2_dechargee():
    """🎯 { n∈ℕ, HW, HN } ⊢ (succ n)!_déf2 = (n!_déf2)·(succ n) — 3 hyps,
    theorie==22 après.  (Miroirs H2/H3 et cible assertés DANS le module.)"""
    th = factorielle_def2_dechargee()
    assert len(th.hypotheses) == 3
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_factorielle_def2_ultime():
    """🎯🎯 { n∈ℕ } ⊢ (succ n)!_déf2 = (n!_déf2)·(succ n) — 1 hyp : LE PARAMÈTRE.
    (HW/HN dérivées par réflexivité post-migration ; miroirs assertés au module.)"""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_factorielle_def2_close import factorielle_def2_ultime
    th = factorielle_def2_ultime()
    assert th.hypotheses == frozenset({appartient(var("nfr"), ensemble_NN())})
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
