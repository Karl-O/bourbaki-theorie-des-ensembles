"""Tests §III.6 — ℵ₀ = Card(NN), route Cantor-Bernstein vers ℵ₀ = ℵ₀+1.

🎯🎯🎯 VERROU DE LIANTS LEVÉ par le PONT-α DÉRIVÉ (alpha_bridge) : la forme à liants
SÛRS de l'injectivité/fonctionnalité/inclusion est convertie vers la forme PAR DÉFAUT
exigée par est_injection_de, SANS toucher le noyau.  D'où la chaîne complète :

CLOS (vérifiés est_clos, 0 hyp, conclusion exacte, theorie=22) :
  • successeur_non_nul   ⊢ ¬(successeur(t)=0) ;
  • inf_egal_NN_diff     ⊢ inf_egal_card(NN∖{0}, NN)         (moitié facile) ;
  • s_injective_safe     ⊢ injective_dans(s, NN, m0, m0p)    (math de l'injectivité) ;
  • _dom_s_egal_NN       ⊢ dom(s) = NN ;
  • s_fonctionnel        ⊢ est_fonctionnel(s) ;
  • _image_s_incluse     ⊢ image(s,NN) ⊂ NN∖{0} ;
  • inf_egal_NN          ⊢ inf_egal_card(NN, NN∖{0})         (moitié DURE — verrou levé) ;
  • NN_eq_NN_sans_zero   ⊢ equipotent(NN, NN∖{0})            (Cantor–Bernstein) ;
  • aleph0_egal_succ     ⊢ Card NN = successeur(Card NN)     (ℵ₀ = ℵ₀+1) ;
  • aleph0_infini        ⊢ ¬Fini(ℵ₀)                          (ℕ EST INFINI).

⚠ Les théorèmes profonds (inf_egal_NN et aval) sont LENTS (Prop 8 + N_existe,
τ-cardinaux imbriqués) : marqués @pytest.mark.slow et regroupés en UN test
(les briques lourdes sont mémoïsées → construites une fois par session).
"""
import pytest

from bourbaki.logique.i_1_termes_relations.formule import var, egal, non
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, ZERO, est_fini
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN
from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card, equipotent
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import (
    successeur_non_nul, inf_egal_NN_diff, _NN_sans_zero, s_injective_safe, _s,
    _dom_s_egal_NN, _image_s_incluse, inf_egal_NN, NN_eq_NN_sans_zero,
    aleph0_egal_succ, aleph0_infini, aleph_0,
)
from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_ensemble_NN import ensemble_NN as _NN


def test_theorie_22():
    assert len(E.theorie_ensembles().axiomes) == 22


def test_successeur_non_nul():
    th = successeur_non_nul()                  # binder défaut « j »
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == non(egal(successeur(var("j")), ZERO))
    assert th.conclusion.tag == "non"          # non-vacuous


def test_inf_egal_NN_diff():
    th = inf_egal_NN_diff()
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == inf_egal_card(_NN_sans_zero(), ensemble_NN())
    assert th.conclusion.tag in ("non", "exists")


def test_dom_s_egal_NN():
    """⊢ dom(s) = NN  (translation définie sur tout NN ; via _membre_s + α-pont)."""
    th = _dom_s_egal_NN()
    assert th.est_clos and not th.hypotheses
    assert th.conclusion == egal(E.dom(_s(_NN())), _NN())


@pytest.mark.slow
def test_chaine_aleph0_complete():
    """🎯🎯🎯 La chaîne ℕ-INFINI complète, regroupée (briques lourdes mémoïsées).

    s_injective_safe, s_fonctionnel, _image_s_incluse, inf_egal_NN,
    NN_eq_NN_sans_zero, aleph0_egal_succ, aleph0_infini — TOUS CLOS, 0 hyp, theorie=22."""
    NN = _NN()
    D = _NN_sans_zero()
    s = _s(NN)

    inj = s_injective_safe()
    assert inj.est_clos and inj.conclusion == E.injective_dans(s, NN, "m0", "m0p")

    fonct = s_fonctionnel_thm()
    assert fonct.est_clos and fonct.conclusion == E.est_fonctionnel(s)

    img = _image_s_incluse()
    assert img.est_clos and img.conclusion == E.inclus(E.image(s, NN), D)

    le = inf_egal_NN()
    assert le.est_clos and not le.hypotheses
    assert le.conclusion == inf_egal_card(NN, D)

    eq = NN_eq_NN_sans_zero()
    assert eq.est_clos and not eq.hypotheses
    assert eq.conclusion == equipotent(NN, D)

    succ = aleph0_egal_succ()
    assert succ.est_clos and not succ.hypotheses
    assert succ.conclusion == egal(aleph_0(), successeur(aleph_0()))

    inf = aleph0_infini()
    assert inf.est_clos and not inf.hypotheses
    assert inf.conclusion == non(est_fini(aleph_0()))      # ℕ est INFINI

    assert len(E.theorie_ensembles().axiomes) == 22


def s_fonctionnel_thm():
    from bourbaki.entiers.iii_6_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import s_fonctionnel
    return s_fonctionnel(_NN())


def test_theorie_22_apres():
    assert len(E.theorie_ensembles().axiomes) == 22
