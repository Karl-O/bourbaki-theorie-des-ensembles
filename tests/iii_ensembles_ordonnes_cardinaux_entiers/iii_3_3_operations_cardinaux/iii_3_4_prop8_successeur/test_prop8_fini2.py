"""Tests — PROPOSITION 8 INCONDITIONNELLE (le successeur cardinal est injectif).

Le CAS 2 (transposition) FERME la Proposition 8.  L'HT exigée est la version
CONDITIONNELLE (ht_glob_conditionnel), SUFFISANTE pour le CAS 2 (qui ne consomme HT
que sous bij(h) et h(*)∈B×{0}).  On certifie : HT conditionnelle close, H2 prouvé,
Prop 8 inconditionnelle close.
"""
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.transposition._ht_glob import (
    ht_de_copie_gauche, ht_glob_conditionnel)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.ensembles_prop8_fini2 import (
    cas2_h2, prop8_successeur_injectif)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.ensembles_prop8_assemblage import cas2_hypothese
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.ensembles_prop8_transposition import (
    transposition_hypothese)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import antecedent_consequent


_STAR = E.couple(E.VIDE, E.couple(E.VIDE, E.VIDE))   # * = (∅, 1)


def test_ht_de_copie_gauche_clos():
    th = ht_de_copie_gauche("B")
    assert th.est_clos
    _, cons = antecedent_consequent(th.conclusion)   # (c0∈B×{0}) ⇒ HT(B,c0)
    assert cons.tag == "exists" and cons.lieur == "tau"


def test_ht_de_copie_gauche_match_downstream():
    # le consequent doit COÏNCIDER avec transposition_hypothese (lieur "tau")
    hstar = E.valeur(var("h"), _STAR)
    th = ht_de_copie_gauche("B", hstar, "tau")
    _, cons = antecedent_consequent(th.conclusion)
    assert cons == transposition_hypothese("B", hstar, "tau")


def test_ht_glob_conditionnel_clos():
    assert ht_glob_conditionnel("A", "B").est_clos


def test_cas2_h2_est_H2_prouve():
    th = cas2_h2("A", "B")
    assert th.est_clos
    assert th.conclusion == cas2_hypothese("A", "B")   # le CAS 2, désormais PROUVÉ


def test_prop8_successeur_injectif_clos():
    th = prop8_successeur_injectif("A", "B")
    assert th.est_clos                                  # INCONDITIONNEL
    ant, cons = antecedent_consequent(th.conclusion)    # (succ A=succ B) ⇒ (Card A=Card B)
    assert ant == egal(successeur(var("A")), successeur(var("B")))
    assert cons == egal(cardinal(var("A")), cardinal(var("B")))
