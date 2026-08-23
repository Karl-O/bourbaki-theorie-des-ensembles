# -*- coding: utf-8 -*-
"""Miroir de h2_garde/ensembles_donnees_chaine.py — 2 des 9 données du recollement."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini_ensemble,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_donnees_chaine import (
    pr1_inclus_E, us_inclus_E, us_infini,
)


def test_pr1_inclus_E():
    """{ p ∈ 𝔉(E) } ⊢ pr₁(p) ⊂ E."""
    t = pr1_inclus_E()
    assert len(t.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_us_inclus_E():
    """🎯 { chaîne } ⊢ ⋃S(C) ⊂ E   (donnée 1/9 du recollement)."""
    t = us_inclus_E()
    assert t.conclusion == inclus(union_premiere(var("Cch")), var("E"), "xdc")
    assert len(t.hypotheses) == 1, "hyps : %d" % len(t.hypotheses)
    assert t.conclusion not in t.hypotheses, "VACUOUS"


@pytest.mark.slow
def test_us_infini():
    """🎯 { chaîne, C≠∅ } ⊢ ⋃S(C) infinie   (donnée 2/9).   [~155 s]"""
    vC = var("Cch")
    t = us_infini()
    assert t.conclusion == est_infini_ensemble(union_premiere(vC))
    assert len(t.hypotheses) == 2
    assert non(egal(vC, E.VIDE)) in t.hypotheses, "« C non vide » doit servir"
    assert t.conclusion not in t.hypotheses, "VACUOUS"
