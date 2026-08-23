# -*- coding: utf-8 -*-
"""Miroir de claim/donnees/ensembles_recollement.py — les 11 données branchées."""
import pytest

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, non, appartient,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_recollement import (
    recollement_de_chaine,
)


@pytest.mark.slow
def test_recollement_de_chaine():
    """🎯🎯 { chaîne, C≠∅ } ⊢ (⋃S(C), ⋃𝔇(C)) ∈ 𝔉(E).   [~176 s]

    L'aboutissement des onze données : `frame_de_recollement` les réclamait
    toutes, elles sont toutes dérivées.  Il ne reste que le GARDE de Bourbaki,
    qui est exactement l'antécédent de `donnees_recollement` — l'unique
    hypothèse ouverte de `hess_maximal`."""
    vE, vC = var("E"), var("Cch")
    D, US = famille_de_chaine(vC), union_premiere(vC)
    t = recollement_de_chaine()
    assert t.conclusion == appartient(E.couple(US, union_famille(D)), frame_pair(vE))
    assert set(t.hypotheses) == {
        chaine(frame_ordre(vE), frame_pair(vE), vC, "xmaj", "y", "z"),
        non(egal(vC, E.VIDE))}
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
