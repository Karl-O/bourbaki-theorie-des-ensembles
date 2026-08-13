# -*- coding: utf-8 -*-
"""Test §III.2.5 — pr₂(h) est un segment de F (miroir image).  theorie==22."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_img_segment import (
    temoin_dans_S, img_h_initial_sous_temoin, img_h_initial_cible,
    img_h_est_segment_sous_temoin, img_h_est_segment_cible,
)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_img_h_initial_sous_temoin():
    """{temoin_dans_S} ⊢ initialité de pr₂(h) — 1 hyp, cible miroir, non vacueux."""
    th = img_h_initial_sous_temoin()
    assert th.conclusion == img_h_initial_cible()
    assert th.hypotheses == frozenset({temoin_dans_S()})
    assert th.conclusion not in th.hypotheses


def test_img_h_est_segment_sous_temoin():
    """{temoin_dans_S} ⊢ est_segment(pr₂h, R', F) — 1 hyp, theorie==22 après."""
    th = img_h_est_segment_sous_temoin()
    assert th.conclusion == img_h_est_segment_cible()
    assert th.hypotheses == frozenset({temoin_dans_S()})
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_trichotomie_min2():
    """🎯🎯 Th.3 à 5 hyps SANS segment de construction : {bo, bo, maximalité,
    val_dans_F, temoin_dans_S} — les asserts de forme vivent dans le module."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_img_segment import (
        trichotomie_ordinaux_canon_prouve_min2,
    )
    th = trichotomie_ordinaux_canon_prouve_min2()
    assert len(th.hypotheses) == 5
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22


def test_img_h_est_segment_prouve():
    """🎯 est_segment(pr₂h, R', F) CLOS — temoin_dans_S DÉRIVÉE (pont)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_img_segment import (
        img_h_est_segment_prouve,
    )
    th = img_h_est_segment_prouve()
    assert th.conclusion == img_h_est_segment_cible()
    assert th.est_clos
    assert len(E.theorie_ensembles().axiomes) == 22


def test_trichotomie_min3():
    """🎯🎯🎯 Th.3 aux HYPOTHÈSES DU LIVRE : {bo(R,E), bo(Rp,F), maximalité} —
    les DEUX segments dérivés par les ponts, val_dans_F et temoin_dans_S MORTES."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_img_segment import (
        trichotomie_ordinaux_canon_prouve_min3,
    )
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_dom_segment import val_dans_F
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.trichotomie_ordinaux.assemblage.ensembles_trichotomie_img_segment import temoin_dans_S
    th = trichotomie_ordinaux_canon_prouve_min3()
    assert len(th.hypotheses) == 3
    assert val_dans_F() not in th.hypotheses
    assert temoin_dans_S() not in th.hypotheses
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
