"""Tests §III.5.2 — PROPOSITION 3 (cas binaire, monotonie STRICTE)."""
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop3_strict_mono_iii5 import (
    somme_strict_monotone, somme_strict_monotone_enonce,
    produit_strict_monotone, produit_strict_monotone_enonce,
)
import pytest

#: FICHIER LOURD — 2609 s mesurés le 18 août (pytest --durations).
#: Marqué slow : la porte « not slow » ne le voit plus, mais le théorème
#: reste vérifié par la suite COMPLÈTE — à lancer avant toute annonce.
pytestmark = pytest.mark.slow


def test_theorie_22():
    assert len(theorie_ensembles().axiomes) == 22


def test_somme_strict_monotone_close():
    thm = somme_strict_monotone()
    assert thm.est_clos, f"hypothèses résiduelles : {thm.hypotheses}"
    assert thm.conclusion == somme_strict_monotone_enonce()
    assert len(theorie_ensembles().axiomes) == 22


def test_produit_strict_monotone_close():
    thm = produit_strict_monotone()
    assert thm.est_clos, f"hypothèses résiduelles : {thm.hypotheses}"
    assert thm.conclusion == produit_strict_monotone_enonce()
    assert len(theorie_ensembles().axiomes) == 22
