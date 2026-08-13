"""Tests : divisibilité / parité « propres » sur le vrai produit cardinal."""
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
    divise_propre_reflexif, divise_propre_reflexif_cible,
    pair_ou_impair, pair_ou_impair_cible,
    deux_divise_double, deux_divise_double_cible,
)


def _theorie_intacte():
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
    assert len(theorie_ensembles().axiomes) == 22


def test_divise_propre_reflexif():
    thm = divise_propre_reflexif("adr")
    assert thm.conclusion == divise_propre_reflexif_cible("adr")
    # hyp est_cardinal(a) honnête, conclusion ∉ hyp
    assert thm.conclusion not in thm.hypotheses


def test_pair_ou_impair():
    thm = pair_ou_impair("npi")
    assert thm.conclusion == pair_ou_impair_cible("npi")
    assert thm.est_clos


def test_deux_divise_double():
    thm = deux_divise_double("ydd")
    assert thm.conclusion == deux_divise_double_cible("ydd")
    assert thm.est_clos


def test_theorie():
    _theorie_intacte()
