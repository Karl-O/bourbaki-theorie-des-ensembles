# -*- coding: utf-8 -*-
"""Tests — l'oracle numérique.

⚠️ Ces tests vérifient un outil qui NE DÉMONTRE RIEN. Aucun `Theoreme` ne sort
de l'oracle. Ce qu'on vérifie, c'est qu'il calcule juste et qu'il ne ment pas
dans le sens dangereux : il ne doit JAMAIS affirmer qu'une formule est vraie
alors qu'elle est fausse, et il doit rendre `None` — pas `True` — dès qu'il
sort de son fragment."""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    egal, var,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire as SC,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire as PCB,
)
from outils_ia.arithmetique.numeraux import num
from outils_ia.arithmetique.oracle_num import contre_exemple, table, valeur, verite
from outils_ia.conjectures.goldbach import est_premier

BORNE = 10


def test_valeur_par_table_et_non_par_descente():
    """`N(3)+N(4)` vaut 7 — alors qu'on ne peut PAS descendre dedans.

    Dans ce noyau, `N(7)` et `N(3)+N(4)` sont tous deux des τ-termes à UN
    argument : il n'y a rien à décomposer. L'évaluation passe donc par une
    table bâtie une fois, et le hachage rend chaque test O(1). C'est la loi de
    conception du module, et ce test la verrouille."""
    table(BORNE)
    assert valeur(num(7), borne=BORNE) == 7
    assert valeur(SC(num(3), num(4)), borne=BORNE) == 7
    assert valeur(PCB(num(2), num(3)), borne=BORNE) == 6


def test_verite_sur_les_egalites_et_la_primalite():
    """L'évaluation tranche juste dans les deux sens."""
    table(BORNE)
    assert verite(egal(SC(num(3), num(4)), num(7)), borne=BORNE) is True
    assert verite(egal(SC(num(3), num(4)), num(8)), borne=BORNE) is False
    assert verite(est_premier(num(7), d="d1", q="q1"), borne=BORNE) is True
    assert verite(est_premier(num(9), d="d1", q="q1"), borne=BORNE) is False


def test_hors_fragment_rend_None_et_jamais_True():
    """LE TEST DE SÛRETÉ : hors du fragment, l'oracle se tait.

    Un terme qu'il ne sait pas évaluer doit donner `None`, pas `True`. Un
    oracle qui affirmerait sur ce qu'il ignore serait pire qu'inutile — il
    ferait renoncer à des preuves valides."""
    x = var("xhorsfragment")
    assert verite(egal(x, num(3)), borne=BORNE) is None
    assert valeur(x, borne=BORNE) is None


def test_contre_exemple_trouve_le_faux():
    """`n + n = n·n` est faux dès `n = 1` — l'oracle le trouve.

    C'EST LE SEUL USAGE FIABLE. Un contre-exemple trouvé est une information
    CERTAINE : inutile de dépenser du noyau à vouloir démontrer l'énoncé."""
    n = var("n")
    faux = contre_exemple(egal(SC(n, n), PCB(n, n)), ["n"], borne=6)
    assert faux is not None and faux["n"] in (1, 3, 4, 5, 6)


def test_aucun_contre_exemple_n_est_PAS_une_preuve():
    """Sur un énoncé vrai, l'oracle ne trouve rien — et ça ne prouve rien.

    Le test vérifie le comportement, mais son intitulé porte la garde : cette
    absence n'autorise QUE la dépense de temps de noyau. Goldbach elle-même
    n'a aucun contre-exemple connu jusqu'à 4×10¹⁸."""
    n = var("n")
    assert contre_exemple(egal(SC(n, n), SC(n, n)), ["n"], borne=4) is None
