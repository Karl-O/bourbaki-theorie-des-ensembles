"""Tests — assemblage bijection-recollement de chaîne + frame-membership (§III.6.3)."""
from bourbaki.logique.i_1_termes_relations.formule import var, appartient, et
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.ordre.iii_2_bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille
from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair
from bourbaki.cardinaux.ensembles_chaine_frame_membership import (
    union_chaine_est_bijection, union_chaine_dans_frame,
)


def test_union_chaine_est_bijection():
    th = union_chaine_est_bijection("Dchaine", "USchaine")
    U = union_famille(var("Dchaine"))
    US = var("USchaine")
    Prod = E.produit(US, US)
    assert th.conclusion == est_bijection_de(U, Prod, US)
    assert th.conclusion not in th.hypotheses        # non vacuous


def test_union_chaine_dans_frame():
    th = union_chaine_dans_frame("E", "Dchaine", "USchaine")
    U = union_famille(var("Dchaine"))
    US = var("USchaine")
    p = E.couple(US, U)
    assert th.conclusion == appartient(p, frame_pair(var("E")))
    assert th.conclusion not in th.hypotheses        # non vacuous


def test_frame_inductif_chaine():
    from bourbaki.ordre.iii_2_bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif
    from bourbaki.cardinaux.ensembles_hessenberg_hard import frame_pair, frame_ordre
    from bourbaki.cardinaux.ensembles_chaine_frame_membership import frame_inductif_chaine
    th = frame_inductif_chaine("E")
    Gam, Fr = frame_ordre(var("E")), frame_pair(var("E"))
    assert th.conclusion == est_inductif(Gam, Fr, "C", "m", "x", "y", "z")
    assert th.conclusion not in th.hypotheses


def test_theorie_inchangee():
    from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_abrege import theorie_ensembles
    assert len(theorie_ensembles().axiomes) == 22
