"""Tests §III.6.3 — recollement de CHAÎNE : injectivité + assemblage graphe-niveau."""
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille, famille_compatible
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_recollement_famille_injectif import (
    injectif_graphe, famille_dirigee, membres_injectifs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_union_chaine_bijection import (
    union_chaine_injective, union_chaine_bijection_graphe,
)


def test_theorie_inchangee_22():
    assert len(theorie_ensembles().axiomes) == 22


def test_union_chaine_injective():
    th = union_chaine_injective("Dchaine")
    U = union_famille(N.var("Dchaine"))
    assert th.conclusion == injectif_graphe(U)
    assert famille_dirigee(N.var("Dchaine")) in th.hypotheses
    assert membres_injectifs(N.var("Dchaine")) in th.hypotheses
    assert th.conclusion not in th.hypotheses


def test_union_chaine_bijection_graphe():
    th = union_chaine_bijection_graphe("Dchaine")
    vD = N.var("Dchaine")
    U = union_famille(vD)
    assert th.conclusion == E.et(E.est_fonctionnel(U), injectif_graphe(U))
    assert famille_compatible(vD) in th.hypotheses
    assert famille_dirigee(vD) in th.hypotheses
    assert membres_injectifs(vD) in th.hypotheses
    assert th.conclusion not in th.hypotheses
