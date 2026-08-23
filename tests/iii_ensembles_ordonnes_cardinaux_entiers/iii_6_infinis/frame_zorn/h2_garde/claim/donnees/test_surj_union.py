# -*- coding: utf-8 -*-
"""Miroir de claim/donnees/ensembles_surj_union.py — donnée 7/11."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, existe, impl, pourtout, appartient,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_surj_union import (
    surj_union_us,
)


def test_surj_union_us():
    """🎯 { chaîne } ⊢ (∀w)( w ∈ US ⇒ (∃p)( p∈𝔇 et (∃a)((a,w)∈p) ) )  (donnée 7/11).

    Elle INVERSE la mécanique des données (9) et (10) : au lieu de défaire une
    appartenance pour remonter à un membre, elle doit en PRODUIRE un."""
    vC, vw, vp = var("Cch"), var("wsj"), var("psj")
    D, US = famille_de_chaine(vC), union_premiere(vC)
    corps = et(appartient(vp, D),
               existe("asj", appartient(E.couple(var("asj"), vw), vp)))
    t = surj_union_us()
    assert t.conclusion == pourtout("wsj", impl(appartient(vw, US),
                                                existe("psj", corps)))
    assert len(t.hypotheses) == 1
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
