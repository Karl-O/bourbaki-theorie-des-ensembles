# -*- coding: utf-8 -*-
"""Miroir de claim/donnees/ensembles_img_union.py — donnée 10/11."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, inclus,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_img_union import (
    img_union_inclus_us,
)


def test_img_union_inclus_us():
    """🎯 { chaîne } ⊢ image(⋃𝔇(C), US×US) ⊂ US   (donnée 10/11).

    Jumelle de la (9) : même descente en trois existentielles, mais l'axiome de
    l'IMAGE au départ et `valeur_dans_pr1` à l'arrivée."""
    vC = var("Cch")
    U, US = union_famille(famille_de_chaine(vC)), union_premiere(vC)
    t = img_union_inclus_us()
    assert t.conclusion == inclus(E.image(U, E.produit(US, US)), US, "wiu")
    assert len(t.hypotheses) == 1
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
