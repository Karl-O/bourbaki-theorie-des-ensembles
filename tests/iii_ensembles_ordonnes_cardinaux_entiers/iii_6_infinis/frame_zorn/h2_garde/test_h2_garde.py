# -*- coding: utf-8 -*-
"""Tests H2 (pas 1-2) — le résidu gardé + l'énoncé de chaîne majorée sous H1."""
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_inductivite import (
    enonce_chaine_majoree,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_maximal_clos import (
    residu_H1,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_h2_garde import (
    m_dans_frame_garde, enonce_chaine_majoree_garde,
)


def test_enonce_chaine_majoree_garde():
    """🎯 {résidu gardé, H1} ⊢ enonce_chaine_majoree(Γ𝔉,𝔉) — C=∅ réglé."""
    t = enonce_chaine_majoree_garde("E")
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var
    Gam, Fr = frame_ordre(var("E")), frame_pair(var("E"))
    assert t.conclusion == enonce_chaine_majoree(Gam, Fr, "C", "m", "xmaj", "y", "z")
    assert set(t.hypotheses) == {m_dans_frame_garde("E"), residu_H1("E")}
    assert len(E.theorie_ensembles().axiomes) == 22
