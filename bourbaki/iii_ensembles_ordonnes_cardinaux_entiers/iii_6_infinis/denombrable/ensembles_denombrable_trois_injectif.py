# -*- coding: utf-8 -*-
"""§III.6 (prérequis Lemme 2) — W4 : l'application n ↦ 3^n est INJECTIVE sur ℕ.

🎯 CIBLE (trois_puiss_injectif) :
    ⊢ Fini n ⇒ (∀np)( (Fini np ∧ 3^n = 3^np) ⇒ n = np ).

Récurrence C61 sur n (patron deux_valuation_unique, allégé : un seul ∀ interne).
Le cœur absurde : 1 = 3^(succ j) est IMPOSSIBLE — arithmétique du successeur :
    1 = 3^(succ j) = 3^j·3 = 3·3^j = 3·succ(i)   [prédécesseur de 3^j ≠ 0]
      = 3·i + 3 = succ(3·i + 2)                  [produit/somme_succ_distribue]
    ⇒ succ(0) = succ(3i+2) ⇒ 0 = 3i+2 = succ(3i+1)   [Prop. 8 + Card-id]
    ⇒ contradiction avec successeur_non_nul.
Dans le pas, 3^n·3 = 3^j·3 se simplifie par 3 (W2, 3 = succ 2 ≠ 0).

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro, conjonction_elim_gauche as elg,
    conjonction_elim_droite as eld, tiers_exclu, cas, equivalence_avant,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, inf_strict_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (
    _ex_falso,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur, ZERO, UN, DEUX, TROIS,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_trois_quatre import (
    fini_trois,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_zero import (
    zero_est_un_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
    fini_successeur_implique_fini, _card_idempotent_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import (
    successeur_non_nul,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
    _fini_et_P_implique_succ,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (
    produit_succ_distribue,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import (
    somme_succ_distribue,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_parite_iii5 import (
    _prop8_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_puissance_deux_trois_NN import (
    trois_puissance_dans_NN,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_valuation_iii6 import (
    puissance_non_nulle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_deux_valuation import (
    ops_produit_commutatif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_injection_iii6 import (
    puissance_succ_eq_incond, simplification_multiplicative,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_valuation_recurrence import (
    exposant_zero_un, _card_est_cardinal_t, _card_deux,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, pr):
    return N.modus_ponens(pr, N.loi_deduction(hyp, thm))


def _exp3(s):
    """3^s   (exposant cardinal, base TROIS)."""
    return exposant_cardinal_binaire(TROIS, _t(s))


def _prod(a, b):
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
        produit_cardinal_binaire)
    return produit_cardinal_binaire(_t(a), _t(b))


def _card_trois():
    """⊢ est_cardinal(TROIS)   (TROIS = Card(DEUX⊔{∅}) littéralement)."""
    return _card_est_cardinal_t(somme_disjointe(DEUX, E.singleton(E.VIDE)))


def _card_un():
    """⊢ est_cardinal(UN)   (UN = Card(ZERO⊔{∅}) littéralement)."""
    return _card_est_cardinal_t(somme_disjointe(ZERO, E.singleton(E.VIDE)))


def _fini_exp3(ts, fini_s):
    """{fini_s ⊢ Fini s} ⊢ Fini(3^s)."""
    g = N.generalisation("npdt", trois_puissance_dans_NN("npdt"))
    return N.modus_ponens(fini_s, instancie(g, _t(ts)))


def _nn_exp3(ts, fini_s):
    """{fini_s ⊢ Fini s} ⊢ ¬(3^s = 0)."""
    inner = somme_disjointe(DEUX, E.singleton(E.VIDE))
    g = N.generalisation("npnz",
        puissance_non_nulle(inner, successeur_non_nul(DEUX), "npnz"))
    return N.modus_ponens(fini_s, instancie(g, _t(ts)))


def _pse3(ts, fini_s):
    """{fini_s ⊢ Fini s} ⊢ 3^(succ s) = 3^s·3."""
    g = N.generalisation("Apsi", N.generalisation("Npsi",
        puissance_succ_eq_incond("Apsi", "Npsi")))
    pse = instancie(instancie(g, TROIS), _t(ts))
    return N.modus_ponens(conjonction_intro(_card_trois(), fini_s), pse)


def _simplifier(ta, tb, tc, fa, fb, fc, nnc, eq_acbc):
    """de a·c = b·c : ⊢ a = b   (W2 ∀-clos aux termes)."""
    g = N.generalisation("asm", N.generalisation("bsm", N.generalisation(
        "csm", simplification_multiplicative("asm", "bsm", "csm"))))
    inst3 = instancie(instancie(instancie(g, _t(ta)), _t(tb)), _t(tc))
    conj = conjonction_intro(
        conjonction_intro(fa, conjonction_intro(fb, fc)),
        conjonction_intro(nnc, eq_acbc))
    return N.modus_ponens(conj, inst3)


def _fini_k_de(vb, vk, b_eq, card_k, fb):
    """{b_eq ⊢ b=succ k ; card_k ; fb ⊢ Fini b} ⊢ Fini k."""
    leib = N.s6(vb, successeur(vk), "wfk", est_fini(var("wfk")))
    fini_succk = N.modus_ponens(fb, equivalence_avant(N.modus_ponens(b_eq, leib)))
    fsif = instancie(N.generalisation("afsk",
        fini_successeur_implique_fini("afsk")), vk)
    return N.modus_ponens(fini_succk, N.modus_ponens(card_k, fsif))


def _corps_pred(vb, kn="kpred"):
    vkp = var(kn)
    return et(et(egal(vb, successeur(vkp)), est_cardinal(vkp)),
              inf_strict_card(vkp, vb))


def _absurde_un_egal_3succ(tj, fini_j, h_un_eq, cible):
    """{fini_j ⊢ Fini j ; h_un_eq ⊢ 1 = 3^(succ j)} ⊢ cible   (le cœur absurde)."""
    #   lieur interne DISTINCT (kpred2) : le témoin j de l'appelant est souvent
    #   son propre kpred — réutiliser « kpred » ici bloquerait l'élimination
    vj = _t(tj)
    vkp = var("kpred2")
    Q = _exp3(vj)
    #   1 = 3^succj = 3^j·3 = 3·3^j = 3·Q
    chaine0 = composer_egalites(composer_egalites(
        h_un_eq, _pse3(vj, fini_j)),
        ops_produit_commutatif(Q, TROIS))                    # 1 = 3·Q
    #   prédécesseur de Q (≠ 0, fini)
    pred = N.modus_ponens(
        conjonction_intro(_fini_exp3(vj, fini_j), _nn_exp3(vj, fini_j)),
        instancie(predecesseur_fini_universel_preuve(k="kpred2"), Q))
    hK = N.assume(_corps_pred(Q, "kpred2"))
    q_eq = elg(elg(hK))                                      # Q = succ i  (i = kpred)
    card_i = eld(elg(hK))
    #   3·Q = 3·succ i = 3i+3 = succ(3i+2)
    cong_q = N.modus_ponens(q_eq, congruence_terme(
        Q, successeur(vkp), _prod(TROIS, var("wdv")), "wdv"))    # 3·Q = 3·succ i
    g_psd = N.generalisation("Apsd", N.generalisation("Npsd",
        produit_succ_distribue("Apsd", "Npsd")))
    psd = N.modus_ponens(conjonction_intro(_card_trois(), card_i),
                         instancie(instancie(g_psd, TROIS), vkp))   # 3·succ i = 3i+3
    trois_i = _prod(TROIS, vkp)
    card_3i = _card_est_cardinal_t(E.produit(TROIS, vkp))
    g_ssd = N.generalisation("Asd", N.generalisation("Bsd",
        somme_succ_distribue("Asd", "Bsd")))
    ssd = N.modus_ponens(conjonction_intro(card_3i, _card_deux()),
                         instancie(instancie(g_ssd, trois_i), DEUX))
    #   3i + succ(2) = succ(3i+2)   (3 = succ 2 littéral)
    chaine = composer_egalites(composer_egalites(composer_egalites(
        chaine0, cong_q), psd), ssd)                         # 1 = succ(3i+2)
    #   1 = succ(0) littéral ⇒ succ(0) = succ(3i+2) ⇒ 0 = 3i+2   (Prop.8 + Card-id)
    s2 = somme_cardinale_binaire(trois_i, DEUX)              # 3i+2
    prop8 = N.modus_ponens(chaine, _prop8_t(ZERO, s2))       # Card 0 = Card(3i+2)
    card0 = N.modus_ponens(zero_est_un_cardinal(), __cdc(ZERO))   # Card 0 = 0
    idem = _card_idempotent_t(somme_disjointe(trois_i, DEUX))     # Card(3i+2) = 3i+2
    zero_eq = composer_egalites(composer_egalites(
        N.modus_ponens(card0, symetrie(cardinal(ZERO), ZERO)), prop8), idem)
    #   0 = 3i+2 = 3i + succ(1) = succ(3i+1)
    ssd2 = N.modus_ponens(conjonction_intro(card_3i, _card_un()),
                          instancie(instancie(g_ssd, trois_i), UN))
    zero_eq_succ = composer_egalites(zero_eq, ssd2)          # 0 = succ(3i+1)
    succ_eq_zero = N.modus_ponens(zero_eq_succ, symetrie(
        ZERO, successeur(somme_cardinale_binaire(trois_i, UN))))
    nn = successeur_non_nul(somme_cardinale_binaire(trois_i, UN))
    absurd = _ex_falso(succ_eq_zero, nn, cible)
    exk = existe_elimination(N.loi_deduction(_corps_pred(Q, "kpred2"), absurd),
                             "kpred2")
    return N.modus_ponens(pred, exk)


def __cdc(t):
    """cardinal_de_cardinal au terme (implication close)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
        cardinal_de_cardinal)
    return cardinal_de_cardinal(_t(t))


def _ANTE3(b):
    vnp = var("npv")
    return et(est_fini(vnp), egal(_exp3(_t(b)), _exp3(vnp)))


def _P3(b):
    return pourtout("npv", impl(_ANTE3(b), egal(_t(b), var("npv"))))


def trois_puiss_injectif(n="ntj", k="ktj"):
    """🎯 ⊢ Fini n ⇒ (∀np)( (Fini np ∧ 3^n = 3^np) ⇒ n = np ).   (W4, C61.)"""
    vnp = var("npv")
    vkp = var("kpred")
    vn = var(n)
    P = _P3

    # ── P[0] ──────────────────────────────────────────────────────────────────
    h0 = N.assume(_ANTE3(ZERO))
    fnp, eq0 = elg(h0), eld(h0)                              # Fini np ; 3^0 = 3^np
    te0 = tiers_exclu(egal(vnp, ZERO))
    ha = N.assume(egal(vnp, ZERO))
    brA0 = N.loi_deduction(egal(vnp, ZERO),
                           N.modus_ponens(ha, symetrie(vnp, ZERO)))   # 0 = np
    hb = N.assume(non(egal(vnp, ZERO)))
    pred0 = N.modus_ponens(conjonction_intro(fnp, hb),
                           instancie(predecesseur_fini_universel_preuve(), vnp))
    hK0 = N.assume(_corps_pred(vnp))
    np_eq = elg(elg(hK0))                                    # np = succ j
    card_j = eld(elg(hK0))
    fini_j = _fini_k_de(vnp, vkp, np_eq, card_j, fnp)
    #   1 = 3^0 = 3^np = 3^succ j
    cong0 = N.modus_ponens(np_eq, congruence_terme(
        vnp, successeur(vkp), _exp3(var("wdv")), "wdv"))     # 3^np = 3^succj
    un_eq = composer_egalites(composer_egalites(
        N.modus_ponens(exposant_zero_un(TROIS), symetrie(_exp3(ZERO), UN)),
        eq0), cong0)                                         # 1 = 3^succ j
    absurd0 = _absurde_un_egal_3succ(vkp, fini_j, un_eq, egal(ZERO, vnp))
    exk0 = existe_elimination(N.loi_deduction(_corps_pred(vnp), absurd0), "kpred")
    brB0 = N.loi_deduction(non(egal(vnp, ZERO)), N.modus_ponens(pred0, exk0))
    p0 = N.generalisation("npv", N.loi_deduction(_ANTE3(ZERO), cas(te0, brA0, brB0)))
    assert p0.conclusion == P(ZERO), "trois_puiss_injectif : P[0] mal formé"

    # ── pas ───────────────────────────────────────────────────────────────────
    h2 = N.assume(et(est_fini(vn), P(vn)))
    fn, Pn = elg(h2), eld(h2)
    hA = N.assume(_ANTE3(successeur(vn)))
    fnp, eqs = elg(hA), eld(hA)                              # 3^(succ n) = 3^np
    te1 = tiers_exclu(egal(vnp, ZERO))
    #   A : np = 0  →  1 = 3^(succ n) absurde
    ha1 = N.assume(egal(vnp, ZERO))
    cong_a1 = N.modus_ponens(ha1, congruence_terme(
        vnp, ZERO, _exp3(var("wdv")), "wdv"))                # 3^np = 3^0
    un_eq1 = composer_egalites(composer_egalites(
        N.modus_ponens(exposant_zero_un(TROIS), symetrie(_exp3(ZERO), UN)),
        N.modus_ponens(cong_a1, symetrie(_exp3(vnp), _exp3(ZERO)))),
        N.modus_ponens(eqs, symetrie(_exp3(successeur(vn)), _exp3(vnp))))
    #   1 = 3^0 = 3^np = 3^(succ n)
    absurd1 = _absurde_un_egal_3succ(vn, fn, un_eq1, egal(successeur(vn), vnp))
    brA1 = N.loi_deduction(egal(vnp, ZERO), absurd1)
    #   B : np = succ j  →  simplifier par 3, récurrence
    hb1 = N.assume(non(egal(vnp, ZERO)))
    pred1 = N.modus_ponens(conjonction_intro(fnp, hb1),
                           instancie(predecesseur_fini_universel_preuve(), vnp))
    hK1 = N.assume(_corps_pred(vnp))
    np_eq1 = elg(elg(hK1))                                   # np = succ j
    card_j1 = eld(elg(hK1))
    fini_j1 = _fini_k_de(vnp, vkp, np_eq1, card_j1, fnp)
    cong_b1 = N.modus_ponens(np_eq1, congruence_terme(
        vnp, successeur(vkp), _exp3(var("wdv")), "wdv"))     # 3^np = 3^succ j
    #   3^n·3 = 3^(succ n) = 3^np = 3^succ j = 3^j·3
    eq_33 = composer_egalites(composer_egalites(composer_egalites(
        N.modus_ponens(_pse3(vn, fn), symetrie(_exp3(successeur(vn)),
                                               _prod(_exp3(vn), TROIS))),
        eqs), cong_b1), _pse3(vkp, fini_j1))                 # 3^n·3 = 3^j·3
    eq_nj = _simplifier(_exp3(vn), _exp3(vkp), TROIS,
                        _fini_exp3(vn, fn), _fini_exp3(vkp, fini_j1), fini_trois(),
                        successeur_non_nul(DEUX), eq_33)     # 3^n = 3^j
    rec_ante = conjonction_intro(fini_j1, eq_nj)
    n_eq_j = N.modus_ponens(rec_ante, instancie(Pn, vkp))    # n = j
    cong_s = N.modus_ponens(n_eq_j, congruence_terme(
        vn, vkp, successeur(var("wdv")), "wdv"))             # succ n = succ j
    m_eq1 = composer_egalites(cong_s,
        N.modus_ponens(np_eq1, symetrie(vnp, successeur(vkp))))   # succ n = np
    exk1 = existe_elimination(N.loi_deduction(_corps_pred(vnp), m_eq1), "kpred")
    brB1 = N.loi_deduction(non(egal(vnp, ZERO)), N.modus_ponens(pred1, exk1))
    corps_pas = N.generalisation("npv",
        N.loi_deduction(_ANTE3(successeur(vn)), cas(te1, brA1, brB1)))
    step = N.generalisation(n, N.loi_deduction(et(est_fini(vn), P(vn)), corps_pas))
    assert step.conclusion == _fini_et_P_implique_succ(P, n), \
        "trois_puiss_injectif : pas mal formé"

    # ── assemblage C61 ────────────────────────────────────────────────────────
    princ = principe_recurrence_preuve(P, n, k=k)
    pfu = predecesseur_fini_universel(k=k)
    if pfu in princ.hypotheses:
        princ = _cut(princ, pfu, predecesseur_fini_universel_preuve(k=k))
    fini_implique_P = N.modus_ponens(conjonction_intro(p0, step), princ)
    res = instancie(fini_implique_P, vn)                     # Fini n ⇒ P[n]
    assert not res.hypotheses, "trois_puiss_injectif : hypothèses résiduelles"
    return res


__all__ = ["trois_puiss_injectif", "_P3"]
