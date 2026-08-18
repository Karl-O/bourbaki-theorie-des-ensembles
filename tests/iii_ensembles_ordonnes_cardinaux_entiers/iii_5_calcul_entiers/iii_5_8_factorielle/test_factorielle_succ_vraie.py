# -*- coding: utf-8 -*-
"""Test §III.5.8 — LA PHRASE DU LIVRE f(succ n) = (succ n)·f(n).  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_2_recursion_c62.ensembles_c62_fonction_globale import fonction_globale
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ_vraie import factorielle_succ_vraie
import pytest

#: FICHIER LOURD — 901 s mesurés le 18 août (pytest --durations).
#: Marqué slow : la porte « not slow » ne le voit plus, mais le théorème
#: reste vérifié par la suite COMPLÈTE — à lancer avant toute annonce.
pytestmark = pytest.mark.slow


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_factorielle_succ_vraie():
    """🎯🎯🎯 f(succ n) = (succ n)·f(n) — 10 hyps, cible RECONSTRUITE À LA MAIN ici
    (on ne compare pas le module à son propre énoncé), theorie==22 après."""
    th = factorielle_succ_vraie()
    vn = var("nfsc")
    f = fonction_globale("Enat", "Vfac62")
    cible = egal(E.valeur(f, successeur(vn)),
                 produit_cardinal_binaire(successeur(vn), E.valeur(f, vn)))
    assert th.conclusion == cible
    assert len(th.hypotheses) == 10
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_factorielle_rs():
    """🎯🎯 (Rs) DÉRIVÉE : (∀n)(Fini n ⇒ f(succ n)=(succ n)·f(n)) — 9 hyps n-closes,
    cible reconstruite à la main (pourtout/impl épelés, pas via le module)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import pourtout, impl
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ_vraie import factorielle_rs
    th = factorielle_rs()
    vn = var("nfac")
    f = fonction_globale("Enat", "Vfac62")
    cible = pourtout("nfac", impl(
        est_fini(vn),
        egal(E.valeur(f, successeur(vn)),
             produit_cardinal_binaire(successeur(vn), E.valeur(f, vn)))))
    assert th.conclusion == cible
    assert len(th.hypotheses) == 9
    assert th.conclusion not in th.hypotheses


def test_factorielle_entier_complet():
    """🎯🎯🎯 (∀n)(Fini n ⇒ Fini f(n)) SANS (R0) ni (Rs) supposées — 10 hyps n-closes,
    theorie==22 après.  LENT (traverse C61 deux fois)."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import pourtout, impl
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ_vraie import factorielle_entier_complet
    th = factorielle_entier_complet()
    vn = var("nfe")
    f = fonction_globale("Enat", "Vfac62")
    cible = pourtout("nfe", impl(est_fini(vn), est_fini(E.valeur(f, vn))))
    assert th.conclusion == cible
    assert len(th.hypotheses) == 10
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
