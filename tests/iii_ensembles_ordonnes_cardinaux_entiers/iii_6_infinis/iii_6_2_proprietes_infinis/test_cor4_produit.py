# -*- coding: utf-8 -*-
"""Miroir de iii_6_2_proprietes_infinis/ensembles_cor4_produit.py.

La moitié PRODUIT du Corollaire 4 : a · b = a pour 1 ≤ b ≤ a et a infini.

C'est ici, et seulement ici, que sert la garde « b non nul » de Bourbaki : le
volet somme s'en passe (a + b ≥ a vaut même pour b = 0), le produit non
(a · 0 = 0 ≠ a). Le test le rend visible en exigeant la liste EXACTE des quatre
hypothèses.
"""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    UN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_cor4_produit import (
    enonce_cor4_produit, cor4_produit,
)


@pytest.mark.slow
def test_cor4_produit():
    """🎯 { Th. 2, A infini, b ≤ Card A, 1 ≤ b } ⊢ Card A · b = Card A.  [~200 s]

    Quatre hypothèses, et quatre exactement. La quatrième — « 1 ≤ b » — est le
    « b non nul » du livre sous la forme dont la preuve a besoin : elle sert à
    établir a = a·1 ≤ a·b, la borne inférieure, qui n'est PAS symétrique de
    celle de la somme (a ≤ a+b se lit sur l'injection gauche, sans garde)."""
    vA, vb = var("A"), var("bc4")
    cA = cardinal(vA)
    t = cor4_produit("A", "bc4")
    assert t.conclusion == enonce_cor4_produit("A", "bc4")
    assert set(t.hypotheses) == {enonce_hessenberg("A"), est_infini(cA),
                                 inf_egal_card(vb, cA), inf_egal_card(UN, vb)}, \
        "hypothèses résiduelles inattendues : %d" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
