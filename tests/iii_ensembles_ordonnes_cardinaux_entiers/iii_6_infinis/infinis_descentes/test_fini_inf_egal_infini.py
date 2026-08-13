"""Tests — « tout cardinal FINI est ≤ tout cardinal INFINI » (E.III.45).

  • fini_inf_egal_infini  : ( Fini n et card n et card 𝔟 et inf 𝔟 ) ⇒ n ≤ 𝔟  (CLOS).
  • deux_inf_egal_infini  : ( card 𝔟 et inf 𝔟 ) ⇒ 2 ≤ 𝔟                     (CLOS).
  • trois_inf_egal_infini : ( card 𝔟 et inf 𝔟 ) ⇒ 3 ≤ 𝔟                     (CLOS).
theorie=22, noyau intact.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, et, impl
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, est_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import est_infini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import DEUX, TROIS

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.infinis_descentes.ensembles_fini_inf_egal_infini import (
    fini_inf_egal_infini, fini_inf_egal_infini_enonce,
    deux_inf_egal_infini, trois_inf_egal_infini,
)


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22


def test_fini_inf_egal_infini_clos():
    t = fini_inf_egal_infini()
    assert t.est_clos
    assert t.conclusion == fini_inf_egal_infini_enonce()
    assert t.conclusion not in t.hypotheses


def test_deux_inf_egal_infini_clos():
    t = deux_inf_egal_infini()
    assert t.est_clos
    vb = var("b")
    assert t.conclusion == impl(et(est_cardinal(vb), est_infini(vb)),
                                inf_egal_card(DEUX, vb))
    assert t.conclusion not in t.hypotheses


def test_trois_inf_egal_infini_clos():
    t = trois_inf_egal_infini()
    assert t.est_clos
    vb = var("b")
    assert t.conclusion == impl(et(est_cardinal(vb), est_infini(vb)),
                                inf_egal_card(TROIS, vb))
    assert t.conclusion not in t.hypotheses
