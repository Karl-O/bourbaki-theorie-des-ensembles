# -*- coding: utf-8 -*-
"""Tests H2 (pas 3a) — inductivité et Zorn sous le résidu gardé + H1."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    est_inductif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_maximal_clos import (
    residu_H1,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_h2_garde import (
    m_dans_frame_garde,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_inductif_garde import (
    frame_inductif_garde, frame_a_maximal_garde,
)


def test_frame_inductif_garde():
    """{résidu gardé, H1} ⊢ est_inductif(Γ𝔉,𝔉)."""
    t = frame_inductif_garde("E")
    Gam, Fr = frame_ordre(var("E")), frame_pair(var("E"))
    assert t.conclusion == est_inductif(Gam, Fr, "C", "m", "xmaj", "y", "z")
    assert set(t.hypotheses) == {m_dans_frame_garde("E"), residu_H1("E")}
    assert len(E.theorie_ensembles().axiomes) == 22


def test_frame_a_maximal_garde():
    """🎯 {résidu gardé, H1} ⊢ (∃m) element_maximal(Γ𝔉,𝔉,m) — Zorn rebranché."""
    t = frame_a_maximal_garde("E")
    Gam, Fr = frame_ordre(var("E")), frame_pair(var("E"))
    assert t.conclusion == existe("m", element_maximal(Gam, Fr, var("m"), "x"))
    assert set(t.hypotheses) == {m_dans_frame_garde("E"), residu_H1("E")}
    assert len(E.theorie_ensembles().axiomes) == 22
