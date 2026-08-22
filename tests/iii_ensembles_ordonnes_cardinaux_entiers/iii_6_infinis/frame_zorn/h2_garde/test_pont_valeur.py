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


def test_surj_riche_et_image():
    """🎯 surjectivité RICHE (a∈US×US) puis image(⋃𝔇, US×US) = US."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_pont_valeur import (
        surj_riche, image_union_egale,
    )
    t1 = surj_riche()
    assert len(t1.hypotheses) == 3
    t2 = image_union_egale()
    U, Prod = union_famille(_D), E.produit(_US, _US)
    assert t2.conclusion == egal(E.image(U, Prod), _US)
    assert len(t2.hypotheses) == 4
    assert len(E.theorie_ensembles().axiomes) == 22


def test_bijection_sans_valeur():
    """🎯🎯 ⊢ est_bijection_de(⋃𝔇, US×US, US) — les 3 hyps VALEUR dérivées."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_bijection_de,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_pont_valeur import (
        inj_valeur, bijection_sans_valeur,
    )
    U, Prod = union_famille(_D), E.produit(_US, _US)
    assert inj_valeur().conclusion == E.injective_dans(U, Prod)
    t = bijection_sans_valeur()
    assert t.conclusion == est_bijection_de(U, Prod, _US)
    # aucune des trois hypothèses VALEUR ne subsiste
    assert egal(E.dom(U), Prod) not in t.hypotheses
    assert E.injective_dans(U, Prod) not in t.hypotheses
    assert E.est_surjective(U, Prod, _US) not in t.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
