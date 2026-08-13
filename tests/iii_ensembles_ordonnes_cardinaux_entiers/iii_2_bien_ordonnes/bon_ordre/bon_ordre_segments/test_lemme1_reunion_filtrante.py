# -*- coding: utf-8 -*-
"""Tests §III.2.1 — Lemme 1 (ordre sur réunion filtrante, E III.17)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
    famille_dirigee)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.bon_ordre_segments.ensembles_lemme1_reunion_filtrante import (
    hypothese_famille_filtrante, hypothese_ordres_coherents, enonce_lemme1_graphe)


def test_filtrante_est_dirigee():
    D = var("Dfam")
    assert hypothese_famille_filtrante(D) == famille_dirigee(D)


def test_coherence_des_ordres():
    Gb, Ga, Xa = var("Gb"), var("Ga"), var("Xa")
    assert hypothese_ordres_coherents(Gb, Ga, Xa) == \
        egal(E.intersection(Gb, E.produit(Xa, Xa)), Ga)


def test_graphe_pivot():
    G, D = var("G"), var("Dgr")
    assert enonce_lemme1_graphe(G, D) == egal(G, union_famille(D))
