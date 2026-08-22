# -*- coding: utf-8 -*-
"""Tests H2 (β) — du niveau couple au niveau valeur (domaine du recollement)."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, inclus,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_surjective_frame import (
    recollement_domaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_pont_valeur import (
    dom_union_egale,
)

_D, _US = var("Dchaine"), var("USchaine")


def test_dom_union_egale():
    """🎯 {recollement_domaine, dom⊂US×US} ⊢ dom(⋃𝔇) = US×US."""
    t = dom_union_egale()
    U, Prod = union_famille(_D), E.produit(_US, _US)
    assert t.conclusion == egal(E.dom(U), Prod)
    assert set(t.hypotheses) == {recollement_domaine(_D, Prod), inclus(E.dom(U), Prod)}
    assert len(E.theorie_ensembles().axiomes) == 22
