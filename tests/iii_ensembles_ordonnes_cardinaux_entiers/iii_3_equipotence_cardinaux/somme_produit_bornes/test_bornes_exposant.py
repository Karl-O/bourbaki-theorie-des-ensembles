"""Tests — bornes exponentielles INCONDITIONNELLES (E.III.3.5).

B1  base_inf_egal_exposant  ⊢ (b≠0) ⇒ (Card a ≤ a^b)
B2  un_inf_egal_exposant    ⊢ (a≠0) ⇒ (1 ≤ a^b),  1 = Card{∅}
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, non, impl
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_egal_card, cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_bornes_exposant import (
    support_base_exposant, base_inf_egal_exposant, un_inf_egal_exposant)

UN = E.singleton(E.VIDE)          # 1 = Card{∅} (la valeur SET)


def test_theorie_inchangee():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_support_base_clos():
    t = support_base_exposant("B", "A")
    assert t.est_clos and len(t.hypotheses) == 0


def test_B1_base_inf_egal_exposant_clean():
    a, b = var("a"), var("b")
    t = base_inf_egal_exposant("a", "b")
    assert t.est_clos and len(t.hypotheses) == 0
    clean = impl(non(egal(b, E.VIDE)),
                 inf_egal_card(cardinal(a), exposant_cardinal_binaire(a, b)))
    assert t.conclusion == clean


def test_B2_un_inf_egal_exposant_clean():
    a, b = var("a"), var("b")
    t = un_inf_egal_exposant("a", "b")
    assert t.est_clos and len(t.hypotheses) == 0
    clean = impl(non(egal(a, E.VIDE)),
                 inf_egal_card(cardinal(UN), exposant_cardinal_binaire(a, b)))
    assert t.conclusion == clean
