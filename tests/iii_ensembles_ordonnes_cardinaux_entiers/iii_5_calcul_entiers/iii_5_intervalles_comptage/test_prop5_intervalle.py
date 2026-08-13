"""Tests Prop 5 (base) §III.5 : cœur (∗) du découpage [0,b+1]=[0,b]∪{b+1}.

Le COEUR pointwise (la décomposition de membre via (∗)) est CLOS.  Le passage à
l'égalité littérale d'ensembles via A1 est un résidu de τ-hygiène (voir module)."""
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_intervalle import (
    _membre_equivalence, membre_equivalence_enonce, _membre_union,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var


def test_membre_equivalence_clos():
    """(∗) appliqué : est_cardinal(b) ⇒ ( z∈[0,b+1] ⇔ z∈([0,b]∪{b+1}) )  CLOS, 0 hyp."""
    t = _membre_equivalence(var("b"), var("zz"))
    assert t.est_clos
    assert len(t.hypotheses) == 0
    assert t.conclusion == membre_equivalence_enonce("b", "zz")


def test_membre_union_clos():
    """z∈([0,b]∪{b+1}) ⇔ ( z∈[0,b] ou z=b+1 )  CLOS, 0 hyp."""
    t = _membre_union(var("b"), var("zz"))
    assert t.est_clos
    assert len(t.hypotheses) == 0


def test_theorie_inchangee():
    assert len(theorie_ensembles().axiomes) == 22
