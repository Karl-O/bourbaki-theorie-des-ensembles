# -*- coding: utf-8 -*-
"""Tests D1a — Card(E⊔{∅}) = Card E et Eq(E⊔{∅}, E) sous est_infini(Card E)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_carte_egale import (
    ensemble_marque, card_idempotent_terme, est_cardinal_du_cardinal,
    carte_w_egale, eq_w_e,
)

_E = var("Eld")


def test_ponts():
    """⊢ Card(Card E)=Card E et ⊢ est_cardinal(Card E) (clos)."""
    t1 = card_idempotent_terme(_E)
    assert t1.conclusion == egal(cardinal(cardinal(_E)), cardinal(_E))
    assert t1.est_clos
    t2 = est_cardinal_du_cardinal(_E)
    assert t2.conclusion == est_cardinal(cardinal(_E))
    assert t2.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_eq_w_e():
    """🎯 D1a : {est_infini(Card E)} ⊢ Card(W)=Card E puis Eq(W, E)."""
    t = carte_w_egale("Eld")
    W = ensemble_marque(_E)
    assert t.conclusion == egal(cardinal(W), cardinal(_E))
    assert list(t.hypotheses) == [est_infini(cardinal(_E))]
    t2 = eq_w_e("Eld")
    assert t2.conclusion == equipotent(W, _E)
    assert list(t2.hypotheses) == [est_infini(cardinal(_E))]
    assert len(E.theorie_ensembles().axiomes) == 22
