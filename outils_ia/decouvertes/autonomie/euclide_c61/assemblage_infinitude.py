# -*- coding: utf-8 -*-
"""L'INFINITUDE DES PREMIERS — l'assemblage n!+1 (EUCLIDE, théorème final).

    ⊢ (∀n)( Fini n ⇒ ∃p( premier p ∧ Fini p ∧ n ≤ p ) )     [enonce_infinitude]

L'argument d'Euclide, verbatim : m := succ(n!) admet un diviseur premier p
(THÉORÈME diviseur_premier_universel — m est fini [F], ≠0 [succ ≤ mort],
≠1 [1 ≤ n! (minorant) + succ injectif Prop.8]). Comparabilité(p, n) :
  · n ≤ p : c'est le témoin — ∃-intro sur « pep » (le lieur de l'énoncé).
  · p ≤ n : ABSURDE — G donne p | n! (p≠0 par micro-F2), H (avec p | m,
    ponts-α qdiv↦w1H/w2H) donne p = 1 = un() (un_egale_card_singleton),
    contre le 1er conjoint de est_premier.
La cible est l'énoncé EXACT de premiers.enonce_infinitude — celui que la
machine a rendu nécessaire (ev.325). Fermé, Euclide est COMPLET."""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[4]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, non, existe,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (  # noqa: E402
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (  # noqa: E402
    symetrie, composer_egalites, congruence_terme, equivalence_avant,
    equivalence_arriere,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import (  # noqa: E402
    ensembles_abrege as E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (  # noqa: E402
    est_cardinal, cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_sup_cardinal import (  # noqa: E402
    comparabilite_cardinaux_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    divise_propre, _card_de_card_t, _pcbd_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    produit_cardinal_binaire, produit_cardinal_commutatif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (  # noqa: E402
    produit_cardinal_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_4_prop8_successeur.ensembles_prop8_fini2 import (  # noqa: E402
    prop8_successeur_injectif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_famille_successeurs import (  # noqa: E402
    factorielle_def2,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini, successeur, UN, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (  # noqa: E402
    fini_implique_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (  # noqa: E402
    fini_zero, zero_est_un_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (  # noqa: E402
    un_egale_card_singleton,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (  # noqa: E402
    fini_implique_fini_successeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (  # noqa: E402
    succ_pas_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (  # noqa: E402
    zero_inf_egal_cardinal,
)
from outils_ia.arithmetique.machine_num import (  # noqa: E402
    NUM, ex_falso, neg_intro, existe_temoin_verifie,
)
from outils_ia.conjectures.goldbach import est_premier, un  # noqa: E402
from outils_ia.decouvertes.autonomie.premiers import enonce_infinitude  # noqa: E402
from outils_ia.decouvertes.autonomie.euclide_c61.envelope import (  # noqa: E402
    diviseur_premier_universel, _corps,
)
from outils_ia.decouvertes.autonomie.euclide_c61.fini_factorielle import (  # noqa: E402
    fini_factorielle,
)
from outils_ia.decouvertes.autonomie.euclide_c61.minorant_factorielle import (  # noqa: E402
    minorant_factorielle,
)
from outils_ia.decouvertes.autonomie.euclide_c61.divise_factorielle import (  # noqa: E402
    divise_factorielle,
)
from outils_ia.decouvertes.autonomie.euclide_c61.diviseur_commun_succ import (  # noqa: E402
    diviseur_commun_succ,
)

mp = N.modus_ponens


def _cut(thm, hyp, preuve_hyp):
    return mp(preuve_hyp, N.loi_deduction(hyp, thm))


def _gen1_t(builder, nom, t):
    return instancie(N.generalisation(nom, builder(nom)), t)


def _fic_t(t):
    return _gen1_t(fini_implique_cardinal, "AficA", t)


def _comm_t(tx, ty):
    g = produit_cardinal_commutatif("XcmA", "YcmA")
    gen = N.generalisation("XcmA", N.generalisation("YcmA", g))
    return instancie(instancie(gen, tx), ty)


def _pz_t(t):
    return _gen1_t(produit_cardinal_zero, "ApzA", t)


def _rw_avant(eq_thm, motif_w, w, thm):
    x, y = eq_thm.conclusion.termes
    return mp(thm, equivalence_avant(mp(eq_thm, N.s6(x, y, w, motif_w))))


def _rw_arriere(eq_thm, motif_w, w, thm):
    x, y = eq_thm.conclusion.termes
    return mp(thm, equivalence_arriere(mp(eq_thm, N.s6(x, y, w, motif_w))))


def _alpha_div(div_thm, td, tn, b_from, b_to):
    """Pont-α : de ⊢ d|n [lieur b_from], ⊢ d|n [lieur b_to]  (4 gestes)."""
    m_q = et(est_fini(var(b_from)),
             egal(tn, produit_cardinal_binaire(td, var(b_from))))
    mat = et(est_fini(var(b_to)),
             egal(tn, produit_cardinal_binaire(td, var(b_to))))
    ex_w = existe_temoin_verifie(N.assume(m_q), mat, var(b_from), b_to)
    return mp(div_thm, existe_elimination(N.loi_deduction(m_q, ex_w), b_from))


def euclide_infinitude(n="nep"):
    """🎯🎯🎯 ⊢ (∀n)( Fini n ⇒ ∃p( premier p ∧ Fini p ∧ n ≤ p ) ).   [EUCLIDE]"""
    vn = var(n)
    hfn = N.assume(est_fini(vn))
    fn = factorielle_def2(vn)
    m = successeur(fn)
    assert UN == successeur(ZERO), "UN n'est pas succ(0) ?!"
    assert NUM(0) == ZERO and un() == cardinal(E.singleton(E.VIDE))

    fini_fn = mp(hfn, instancie(fini_factorielle(), vn))     # Fini(n!)   [F]
    fini_m = mp(fini_fn, _gen1_t(fini_implique_fini_successeur, "AfsA", fn))
    un_le_fn = mp(hfn, instancie(minorant_factorielle(), vn))    # 1 ≤ n!
    card_fn = mp(fini_fn, _fic_t(fn))
    card_fn_eq = mp(card_fn, _card_de_card_t(fn))            # Card n! = n!

    # ── n! ≠ 0 : sinon 1 ≤ 0 = ¬(succ 0 ≤ 0) violé (spie en 0) ─────────────
    hf0 = N.assume(egal(fn, ZERO))
    un_le_0 = _rw_avant(hf0, inf_egal_card(UN, var("wA0")), "wA0", un_le_fn)
    spie0 = mp(fini_zero(), _gen1_t(succ_pas_inf_egal, "Bsp0A", ZERO))
    assert spie0.conclusion == non(inf_egal_card(UN, ZERO))
    fn_ne_0 = neg_intro(egal(fn, ZERO),
                        ex_falso(un_le_0, spie0, non(egal(fn, ZERO))))

    # ── m ≠ 0 : sinon succ(n!) ≤ n! (0 ≤ n! + Leibniz), mort spie(n!) ──────
    hm0 = N.assume(egal(m, ZERO))
    z_le_fn = _cut(zero_inf_egal_cardinal(fn), est_cardinal(fn), card_fn)
    m_le_fn = _rw_arriere(hm0, inf_egal_card(var("wA1"), fn), "wA1", z_le_fn)
    spie_fn = mp(fini_fn, _gen1_t(succ_pas_inf_egal, "BspA", fn))
    m_ne_0 = neg_intro(egal(m, ZERO),
                       ex_falso(m_le_fn, spie_fn, non(egal(m, ZERO))))

    # ── m ≠ 1 : m = 1 ⇒ succ(n!) = succ(0) ⇒ n! = 0 (Prop.8), mort ────────
    ues = un_egale_card_singleton()                          # 1 = Card({∅}) = un()
    assert ues.conclusion == egal(UN, un())
    hm1 = N.assume(egal(m, un()))
    m_eq_UN = composer_egalites(hm1, mp(ues, symetrie(UN, un())))   # m = 1
    #   textuellement : succ(n!) = succ(0) → Prop.8 → Card n! = Card 0
    inj = N.generalisation("A", N.generalisation("B", prop8_successeur_injectif()))
    cards_eq = mp(m_eq_UN, instancie(instancie(inj, fn), ZERO))
    card_0_eq = mp(zero_est_un_cardinal(), _card_de_card_t(ZERO))   # Card 0 = 0
    fn_eq_0 = composer_egalites(composer_egalites(
        mp(card_fn_eq, symetrie(cardinal(fn), fn)), cards_eq), card_0_eq)
    assert fn_eq_0.conclusion == egal(fn, ZERO)
    m_ne_1 = neg_intro(egal(m, un()),
                       ex_falso(fn_eq_0, fn_ne_0, non(egal(m, un()))))

    # ── LE THÉORÈME : ∃pex( premier ∧ Fini ∧ pex | m ) ─────────────────────
    THE = diviseur_premier_universel()
    inst = instancie(THE, m)                                 # Fini m ⇒ (garde ⇒ ∃p…)
    garde = conjonction_intro(conjonction_intro(fini_m, m_ne_0), m_ne_1)
    ex_p = mp(garde, mp(fini_m, inst))
    assert ex_p.conclusion == existe("pex", _corps(m, p="pex"))

    # ── sous le témoin p (lieur pex) ────────────────────────────────────────
    vp = var("pex")
    m_p = _corps(m, p="pex")
    tp = N.assume(m_p)
    prem_p = conjonction_elim_gauche(tp)                     # premier p
    fin_p = conjonction_elim_gauche(conjonction_elim_droite(tp))     # Fini p
    div_pm = conjonction_elim_droite(conjonction_elim_droite(tp))    # p|m [qdiv]
    assert prem_p.conclusion == est_premier(vp, d="dep", q="qep")
    ne_un_p = conjonction_elim_gauche(prem_p)                # ¬(p = un())
    assert ne_un_p.conclusion == non(egal(vp, un()))
    card_p = mp(fin_p, _fic_t(vp))
    cible = existe("pep", et(est_premier(var("pep"), d="dep", q="qep"),
                             et(est_fini(var("pep")),
                                inf_egal_card(vn, var("pep")))))

    # p ≠ 0 (micro-F2 de l'envelope : sinon m = Card(∅×q) = 0, contra m≠0)
    vq = var("qdiv")
    m3 = et(est_fini(vq), egal(m, produit_cardinal_binaire(vp, vq)))
    t3 = N.assume(m3)
    fin_q = conjonction_elim_gauche(t3)
    eq_m = conjonction_elim_droite(t3)
    hz = N.assume(egal(vp, ZERO))
    cong = mp(hz, congruence_terme(vp, ZERO,
                                   cardinal(E.produit(var("wtA"), vq)), w="wtA"))
    m_eq_zq = composer_egalites(eq_m, cong)                  # m = Card(0×q)
    card_q = mp(mp(fin_q, _fic_t(vq)), _card_de_card_t(vq))
    bd0 = mp(conjonction_intro(N.reflexivite(ZERO), card_q),
             _pcbd_t(E.VIDE, vq, ZERO, vq))
    g0, d0 = bd0.conclusion.termes
    m_eq_vq = composer_egalites(m_eq_zq, mp(bd0, symetrie(g0, d0)))
    m_eq_0 = composer_egalites(composer_egalites(
        m_eq_vq, _comm_t(E.VIDE, vq)), _pz_t(vq))            # m = 0
    nz_sous = neg_intro(egal(vp, ZERO),
                        ex_falso(m_eq_0, m_ne_0, non(egal(vp, ZERO))))
    p_ne_0 = mp(div_pm, existe_elimination(N.loi_deduction(m3, nz_sous), "qdiv"))

    # ── comparabilité(p, n) : p ≤ n (absurde) ou n ≤ p (témoin) ────────────
    compar = comparabilite_cardinaux_terme(vp, vn)

    # ABSURDE : p ≤ n → G → p|n! → H (ponts-α) → p = 1 — contre premier p
    hpn = N.assume(inf_egal_card(vp, vn))
    G_t = instancie(N.generalisation("dG", divise_factorielle()), vp)
    allG = mp(conjonction_intro(fin_p, p_ne_0), G_t)         # ∀n'(Fini ⇒ (p≤n' ⇒ p|n'!))
    p_div_fn = mp(hpn, mp(hfn, instancie(allG, vn)))         # p | n!  [qdiv]
    assert p_div_fn.conclusion == divise_propre(vp, fn, q="qdiv")
    p_fn_w1 = _alpha_div(p_div_fn, vp, fn, "qdiv", "w1H")    # p | n!  [w1H]
    p_m_w2 = _alpha_div(div_pm, vp, m, "qdiv", "w2H")        # p | m   [w2H]
    H_t = instancie(instancie(N.generalisation("aH",
        N.generalisation("dH", diviseur_commun_succ())), fn), vp)
    p_eq_UN = mp(conjonction_intro(conjonction_intro(conjonction_intro(
        fini_fn, card_p), p_ne_0), conjonction_intro(p_fn_w1, p_m_w2)), H_t)
    assert p_eq_UN.conclusion == egal(vp, UN)                # p = 1
    p_eq_un = composer_egalites(p_eq_UN, ues)                # p = un()
    brAbs = N.loi_deduction(inf_egal_card(vp, vn),
                            ex_falso(p_eq_un, ne_un_p, cible))

    # TÉMOIN : n ≤ p → ∃-intro sur le lieur « pep » de l'énoncé
    hnp = N.assume(inf_egal_card(vn, vp))
    mt = conjonction_intro(prem_p, conjonction_intro(fin_p, hnp))
    matrice = et(est_premier(var("pep"), d="dep", q="qep"),
                 et(est_fini(var("pep")), inf_egal_card(vn, var("pep"))))
    ex_intro = existe_temoin_verifie(mt, matrice, vp, "pep")
    assert ex_intro.conclusion == cible
    brTem = N.loi_deduction(inf_egal_card(vn, vp), ex_intro)

    r = cas(compar, brAbs, brTem)                            # cible  [m_p, Fini n]
    r2 = mp(ex_p, existe_elimination(N.loi_deduction(m_p, r), "pex"))
    th_n = N.loi_deduction(est_fini(vn), r2)
    TH = N.generalisation(n, th_n)
    assert TH.est_clos and not TH.hypotheses, "euclide_infinitude non clos"
    assert TH.conclusion == enonce_infinitude(), (
        "euclide_infinitude : conclusion != enonce_infinitude()")
    return TH


__all__ = ["euclide_infinitude"]
