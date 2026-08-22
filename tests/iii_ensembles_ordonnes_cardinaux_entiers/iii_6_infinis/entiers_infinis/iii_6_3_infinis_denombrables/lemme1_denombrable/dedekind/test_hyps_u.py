# -*- coding: utf-8 -*-
"""Tests D1c — les quatre hypothèses de u := x↦h((x,0)) sous h_bij."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_donnees_dedekind import (
    u_dedekind,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_hyps_u import (
    dom_u_egal_E, u_inclus_EE, hors_x0, u_injective,
)

_H, _E = var("hdk"), var("Eld")


def test_dom_et_inclusion():
    """⊢ dom u = E (clos) ; {h_bij} ⊢ u ⊂ E×E."""
    U = u_dedekind(_H, _E)
    t1 = dom_u_egal_E()
    assert t1.conclusion == egal(E.dom(U), _E)
    assert t1.est_clos
    t2 = u_inclus_EE()
    assert t2.conclusion == inclus(U, E.produit(_E, _E))
    assert len(t2.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22


def test_hors_et_injective():
    """{h_bij} ⊢ (∀t∈E)(u(t)≠x0) et injective_dans(u, E)."""
    U = u_dedekind(_H, _E)
    t3 = hors_x0()
    assert len(t3.hypotheses) == 1
    t4 = u_injective()
    assert t4.conclusion == E.injective_dans(U, _E)
    assert len(t4.hypotheses) == 1
    assert len(E.theorie_ensembles().axiomes) == 22
