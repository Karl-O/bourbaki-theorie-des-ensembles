# -*- coding: utf-8 -*-
"""Test §III.5.8 — cas successeur, briques 3A.  theorie==22."""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, non, egal, app
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
import bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_abrege as E
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_existence import regle_factorielle
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ import (
    t_fac_en_non_vide, seg_inclus_e, dom_restriction_seg,
)

_T = lambda t: app("Trule", t)


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_t_fac_en_non_vide():
    """Γ ⊢ T_fac(u) = (card(dom u)+1)·u(dom u) sous Γ ⊢ u≠∅ (vraie règle τ-lourde)."""
    T = regle_factorielle()
    u = var("Utest")
    h_nv = N.assume(non(egal(u, E.VIDE)))
    th = t_fac_en_non_vide(T, u, h_nv)
    assert len(th.hypotheses) == 1


def test_seg_inclus_e():
    """⊢ seg(R,E,x) ⊂ E — CLOS."""
    assert seg_inclus_e().est_clos


def test_dom_restriction_seg():
    """{bo, ebf, rc} ⊢ dom(f|seg(x)) = seg(x) — 3 hyps."""
    th = dom_restriction_seg(_T)
    assert len(th.hypotheses) == 3
    assert len(E.theorie_ensembles().axiomes) == 22


def test_u_non_vide():
    """{ZERO∈E, ZERO∈seg(succ n), bo, ebf, rc} ⊢ f|seg(succ n) ≠ ∅ — 5 hyps."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ import u_non_vide
    th = u_non_vide(_T)
    assert len(th.hypotheses) == 5


def test_factorielle_succ_fallback():
    """🎯🎯 f(succ n) = (succ succ n)·u([0,n]) — 9 hyps honnêtes, theorie==22."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_8_factorielle.ensembles_factorielle_succ import factorielle_succ_fallback
    th = factorielle_succ_fallback()
    assert len(th.hypotheses) == 9
    assert th.conclusion not in th.hypotheses
    assert len(E.theorie_ensembles().axiomes) == 22
