# -*- coding: utf-8 -*-
"""Tests K6a — la règle clampée : la borne V déchargée par tiers exclu."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    regle_dans_V,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.ensembles_regle_clampee import (
    clamp_E, regle_clampee, clamp_dans_E, regle_clampee_bornee,
)

_U, _X0, _E = var("uld"), var("xze"), var("Eld")


def test_clamp_dans_E():
    """{x0∈E} ⊢ clamp_E(t) ∈ E."""
    t = clamp_dans_E(var("tld"), _E, _X0)
    assert t.conclusion == appartient(clamp_E(var("tld"), _E, _X0), _E)
    assert list(t.hypotheses) == [appartient(_X0, _E)]
    assert len(E.theorie_ensembles().axiomes) == 22


def test_regle_clampee_bornee():
    """🎯 K6a : {x0∈E} ⊢ regle_dans_V(T_{S_c,x0}, E) — LA borne V déchargée."""
    t = regle_clampee_bornee(_U, _X0, _E)
    T, _ = regle_clampee(_U, _X0, _E)
    assert t.conclusion == regle_dans_V(T, _E)
    assert list(t.hypotheses) == [appartient(_X0, _E)]
    assert len(E.theorie_ensembles().axiomes) == 22
