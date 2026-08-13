"""Tests — assemblage bijection-recollement de chaîne + frame-membership (§III.6.3)."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, appartient, et
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import est_bijection_de
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import union_famille
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_frame_membership import (
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
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import est_inductif
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import frame_pair, frame_ordre
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_frame_membership import frame_inductif_chaine
    th = frame_inductif_chaine("E")
    Gam, Fr = frame_ordre(var("E")), frame_pair(var("E"))
    assert th.conclusion == est_inductif(Gam, Fr, "C", "m", "x", "y", "z")
    assert th.conclusion not in th.hypotheses


def test_theorie_inchangee():
    from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege import theorie_ensembles
    assert len(theorie_ensembles().axiomes) == 22
