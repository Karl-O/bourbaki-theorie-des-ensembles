# -*- coding: utf-8 -*-
"""Tests D1b — le marqueur, x0 := h(m) ∈ E sous la bijection h : W → E."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, appartient,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    est_bijection_de,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_carte_egale import (
    ensemble_marque,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_donnees_dedekind import (
    MARQUEUR, x0_dedekind, marqueur_dans_W, x0_dans_E,
)

_H, _E = var("hdk"), var("Eld")


def test_marqueur_dans_W():
    """⊢ m ∈ W (clos)."""
    t = marqueur_dans_W("Eld")
    assert t.conclusion == appartient(MARQUEUR, ensemble_marque(_E))
    assert t.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_x0_dans_E():
    """🎯 D1b : {est_bijection_de(h, W, E)} ⊢ h(m) ∈ E."""
    t = x0_dans_E("hdk", "Eld")
    assert t.conclusion == appartient(x0_dedekind(_H), _E)
    assert list(t.hypotheses) == [est_bijection_de(_H, ensemble_marque(_E), _E)]
    assert len(E.theorie_ensembles().axiomes) == 22
