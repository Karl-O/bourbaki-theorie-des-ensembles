# -*- coding: utf-8 -*-
"""Miroir de iii_5_2_inegalites_ordre_soustraction/ensembles_diff_cardinale.py.

La différence cardinale PAR CONSTRUCTION — étape 2 de la réparation R-12.

CE QUE CES TESTS ÉTABLISSENT, et qui n'était pas atteignable avant :
`est_cardinal(a − b)`. Pour `diff_somme`, dont le τ ne porte que l'équation,
cette formule n'est PAS dérivable — rien dans « a = b + c » ne contraint c à
être un cardinal. Avec le τ gardé elle coûte une élimination de conjonction.
C'est tout le fond de R-12 : le manque n'était pas un lemme, c'était la
définition.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.soustraction_cardinale.ensembles_diff_cardinale import (
    diff_cardinale, diff_cardinale_garde, diff_cardinale_equation,
)

_GARDES = {est_cardinal(var("adf")), est_cardinal(var("bdf")),
           inf_egal_card(var("bdf"), var("adf"))}


def test_diff_cardinale_garde():
    """🎯 { card a, card b, b ≤ a } ⊢ est_cardinal( a − b ).   [~6 s]

    LA brique que R-12 réclamait. Trois gardes, et trois exactement — toutes
    présentes dans l'énoncé de Bourbaki (E III.37 : b − a se définit pour des
    entiers, donc des cardinaux, avec a ≤ b)."""
    t = diff_cardinale_garde("adf", "bdf")
    assert t.conclusion == est_cardinal(diff_cardinale("adf", "bdf"))
    assert set(t.hypotheses) == _GARDES, \
        "gardes résiduelles inattendues : %d" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22


def test_diff_cardinale_equation():
    """{ card a, card b, b ≤ a } ⊢ a = b + ( a − b ).   [~6 s]

    L'équation caractéristique. `diff_somme` la fournissait déjà ; ce qui est
    neuf est qu'elle vienne AVEC la garde, du même `existe_temoin` — un seul
    passage au témoin canonique livre les deux."""
    va, vb = var("adf"), var("bdf")
    t = diff_cardinale_equation("adf", "bdf")
    assert t.conclusion == egal(va, somme_cardinale_binaire(
        vb, diff_cardinale("adf", "bdf")))
    assert set(t.hypotheses) == _GARDES
    assert len(E.theorie_ensembles().axiomes) == 22
