# -*- coding: utf-8 -*-
"""Miroir de iii_6_2_proprietes_infinis/ensembles_cor4_somme.py.

La moitié SOMME du Corollaire 4 : a + b = a pour b ≤ a et a infini.

Le test vérifie surtout la LISTE EXACTE des hypothèses. C'est le seul moyen de
constater que la route binaire évite bien les familles : si l'une des briques
en réintroduisait une, une hypothèse supplémentaire apparaîtrait ici.
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg import (
    enonce_hessenberg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.iii_6_2_proprietes_infinis.ensembles_cor4_somme import (
    enonce_cor4_somme, cor4_somme,
)


@pytest.mark.slow
def test_cor4_somme():
    """🎯 { Th. 2, A infini, b ≤ Card A } ⊢ Card A + b = Card A.   [~200 s]

    Trois hypothèses, et trois exactement :
      · le Théorème 2, porté et non dérivé (RÈGLE PERF, 5172,8 s) ;
      · l'infinité de A, qui est l'hypothèse de Bourbaki ;
      · la garde b ≤ Card A, qui remplace le terme sup(a,b) — écart de FORME
        assumé, le contenu étant identique.

    `b` n'est PAS supposé cardinal : b ≤ Card A suffit, l'énoncé est donc
    légèrement plus général que celui du livre."""
    vA, vb = var("A"), var("bc4")
    cA = cardinal(vA)
    t = cor4_somme("A", "bc4")
    assert t.conclusion == enonce_cor4_somme("A", "bc4")
    assert set(t.hypotheses) == {enonce_hessenberg("A"), est_infini(cA),
                                 inf_egal_card(vb, cA)}, \
        "hypothèses résiduelles inattendues : %d" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
