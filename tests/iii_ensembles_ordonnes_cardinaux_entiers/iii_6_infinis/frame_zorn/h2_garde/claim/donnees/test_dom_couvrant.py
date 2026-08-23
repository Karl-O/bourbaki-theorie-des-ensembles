# -*- coding: utf-8 -*-
"""Miroir de claim/donnees/ensembles_dom_couvrant.py — donnée 1/11, la dernière."""
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.claim.donnees.ensembles_dom_couvrant import (
    dom_couvrant,
)


def test_dom_couvrant():
    """🎯 { chaîne } ⊢ (∀a)( a ∈ US×US ⇒ (∃p)(p∈𝔇 et (∃w)((a,w)∈p)) )  (1/11).

    La plus composite : deux composantes, deux membres de la chaîne à comparer
    pour les loger dans un seul.  On y emploie le conjoint pr₁ de l'ordre du
    frame — les BASES s'emboîtent — là où les données précédentes utilisaient
    le conjoint pr₂."""
    vC, va, vp = var("Cch"), var("abdm"), var("pdm")
    D, US = famille_de_chaine(vC), union_premiere(vC)
    corps = et(appartient(vp, D),
               existe("wdm", appartient(E.couple(va, var("wdm")), vp)))
    t = dom_couvrant()
    assert t.conclusion == pourtout("abdm", impl(
        appartient(va, E.produit(US, US)), existe("pdm", corps)))
    assert len(t.hypotheses) == 1
    assert t.conclusion not in t.hypotheses, "VACUOUS"
    assert len(E.theorie_ensembles().axiomes) == 22
