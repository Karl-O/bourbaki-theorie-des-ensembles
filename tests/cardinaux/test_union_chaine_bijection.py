"""Tests §III.6.3 — recollement de CHAÎNE : injectivité + assemblage graphe-niveau."""
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille, famille_compatible
from bourbaki.cardinaux.ensembles_recollement_famille_injectif import (
    injectif_graphe, famille_dirigee, membres_injectifs,
)
from bourbaki.cardinaux.ensembles_union_chaine_bijection import (
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
