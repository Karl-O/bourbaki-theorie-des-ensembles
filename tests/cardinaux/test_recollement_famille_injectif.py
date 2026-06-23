"""Tests — union_famille_injective (recollement-injectif version FAMILLE dirigée)."""
from bourbaki.cardinaux.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
    union_famille_injective, famille_dirigee, membres_injectifs, injectif_graphe,
)
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import var


def test_union_famille_injective_certifie():
    th = union_famille_injective()
    D = var("Dinj")
    # conclusion = injectif_graphe(⋃𝔇)
    assert th.conclusion == injectif_graphe(union_famille(D))
    # exactement les 2 hypothèses honnêtes
    assert set(th.hypotheses) == {famille_dirigee(D), membres_injectifs(D)}
    # non vacuous
    assert th.conclusion not in th.hypotheses


def test_theorie_inchangee_22():
    assert len(E.theorie_ensembles().axiomes) == 22
