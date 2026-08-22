# -*- coding: utf-8 -*-
"""§III.6 (prérequis Lemme 2) — 2-VALUATION, étages 2-3 : l'UNICITÉ par récurrence C61.

🎯 CIBLE (deux_valuation_unique, étage 3) :
    ⊢ Fini m ⇒ (∀mp)(∀u)(∀up)( (Fini mp ∧ Fini u ∧ Fini up ∧ impair u ∧ impair up
        ∧ 2^m·u = 2^mp·up) ⇒ (m = mp ∧ u = up) ).

ROUTE (sans AUCUN report — fini_downward est REPORTÉ, l'écart est ÉVITÉ) :
récurrence C61 sur m, patron pair_neq_impair (parite_iii5).  Dans la base et le
pas, CAS sur mp (tiers exclu mp=0) : mp=0 se traite par le NEUTRE x·1=x et
2^0=1 ; mp≠0 par le PRÉDÉCESSEUR mp=succ j (Fini mp est une hypothèse du corps
— c'est ce qui évite fini_downward), Fini j par fini_successeur_implique_fini.

CE MODULE (étage 2a) : les fondations locales —
  • exposant_zero_un(base)          ⊢ base^0 = 1        [B0 + exposant_zero + 1=Card{∅}] ;
  • ops_produit_un_droite(x, card_x) ⊢ x·1 = x           [Eq(1,{∅}) + produit_cardinal_un] ;
  • _double(s, x, fini_s)           ⊢ 2^(succ s)·x = 2·(2^s·x) ;
  • _simplifier(...)                a·c = b·c ⇒ a = b    [W2 ∀-clos aux termes] ;
  • _temoin_pair(x, Q, eq, fini_Q)  ⊢ 2 | x  (S5 au témoin Q).

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, _prop1_direct_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import (
    eq_produit_invariant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire, exposant_zero_egale_un,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (
    est_fini, successeur, ZERO, UN, DEUX,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (
    un_egale_card_singleton,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_valuation_iii6 import (
    deux_puissance_non_nulle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_deux_valuation import (
    ops_produit_commutatif, ops_produit_associatif, _eq_card_t, _eq_sym_t, _eq_refl_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.denombrable.ensembles_denombrable_injection_iii6 import (
    puissance_succ_eq_incond, simplification_multiplicative,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_puissance_entiers_inconditionnel import (
    B0_preuve,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _exp2(s):
    """2^s   (exposant cardinal, base DEUX)."""
    return exposant_cardinal_binaire(DEUX, _t(s))


def _prod(a, b):
    return produit_cardinal_binaire(_t(a), _t(b))


def _card_est_cardinal_t(tX):
    """⊢ est_cardinal(Card X)  (version TERME, patron denombrable_injection)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (
        card_est_un_cardinal)
    return instancie(N.generalisation("Xcuc3",
        card_est_un_cardinal("Xcuc3", lieur="X")), _t(tX))


def _card_deux():
    """⊢ est_cardinal(DEUX)   (DEUX = Card(UN⊔{∅}) littéralement)."""
    return _card_est_cardinal_t(somme_disjointe(UN, E.singleton(E.VIDE)))


def exposant_zero_un(base):
    """⊢ base^0 = 1.   (B0_preuve + exposant_zero_egale_un + 1 = Card{∅} sym.)"""
    vb = _t(base)
    card_un = cardinal(E.singleton(E.VIDE))
    res = composer_egalites(composer_egalites(
        B0_preuve(vb), exposant_zero_egale_un(vb)),
        N.modus_ponens(un_egale_card_singleton(), symetrie(UN, card_un)))
    assert res.conclusion == egal(exposant_cardinal_binaire(vb, ZERO), UN)
    return res


def ops_produit_un_droite(x, card_x_thm):
    """{card_x_thm ⊢ est_cardinal(x)} ⊢ x·1 = x.

    x·1 = Card(x×UN) ; Eq(UN, {∅}) (1=Card{∅} + Eq(Card{∅},{∅}), Leibniz S6)
    poussée par eq_produit_invariant ⇒ Card(x×UN) = Card(x×{∅}) = Card(x)
    (produit_cardinal_un ∀-clos) = x (cardinal_de_cardinal sous card x)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        equivalence_arriere)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_petits import (
        produit_cardinal_un)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
        cardinal_de_cardinal)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        equipotent)
    vx = _t(x)
    sing = E.singleton(E.VIDE)
    card_sing = cardinal(sing)
    # Eq(UN, {∅}) : Eq(Card{∅}, {∅}) transportée par UN = Card{∅} (Leibniz S6)
    eq_cs = _eq_sym_t(_eq_card_t(sing), sing, card_sing)       # Eq(Card{∅}, {∅})
    leib = N.modus_ponens(un_egale_card_singleton(),
                          N.s6(UN, card_sing, "wpu", equipotent(var("wpu"), sing)))
    eq_un_sing = N.modus_ponens(eq_cs, equivalence_arriere(leib))   # Eq(UN, {∅})
    # Card(x×UN) = Card(x×{∅})
    inv = eq_produit_invariant("F", "G", vx, UN, vx, sing)
    eq_prod = N.modus_ponens(conjonction_intro(_eq_refl_t(vx), eq_un_sing), inv)
    g1 = N.modus_ponens(eq_prod, _prop1_direct_t(E.produit(vx, UN),
                                                 E.produit(vx, sing)))
    # Card(x×{∅}) = Card(x)   (∀-clos au terme, nom frais)
    g2 = instancie(N.generalisation("Apcu", produit_cardinal_un("Apcu")), vx)
    # Card(x) = x
    g3 = N.modus_ponens(card_x_thm, cardinal_de_cardinal(vx))
    res = composer_egalites(composer_egalites(g1, g2), g3)
    assert res.conclusion == egal(_prod(vx, UN), vx), \
        f"ops_produit_un_droite : conclusion inattendue\n{res.conclusion}"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  Helpers de la récurrence
# ══════════════════════════════════════════════════════════════════════════════
def _impair(x):
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
        est_impair_propre)
    return est_impair_propre(_t(x))


def _pair(x):
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (
        est_pair_propre)
    return est_pair_propre(_t(x))


def _fini_exp(ts, fini_s):
    """{fini_s ⊢ Fini s} ⊢ Fini(2^s)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_puissance_deux_trois_NN import (
        deux_puissance_dans_NN)
    g = N.generalisation("npdt", deux_puissance_dans_NN("npdt"))
    return N.modus_ponens(fini_s, instancie(g, _t(ts)))


def _nn_exp(ts, fini_s):
    """{fini_s ⊢ Fini s} ⊢ ¬(2^s = 0)."""
    g = N.generalisation("npnz", deux_puissance_non_nulle("npnz"))
    return N.modus_ponens(fini_s, instancie(g, _t(ts)))


def _fini_prod(ta, tb, fa, fb):
    """{fa ⊢ Fini a, fb ⊢ Fini b} ⊢ Fini(a·b)."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (
        produit_binaire_entier)
    g = N.generalisation("apbe", N.generalisation("bpbe",
        produit_binaire_entier("apbe", "bpbe")))
    return N.modus_ponens(conjonction_intro(fa, fb),
                          instancie(instancie(g, _t(ta)), _t(tb)))


def _double(ts, tx, fini_s):
    """{fini_s ⊢ Fini s} ⊢ 2^(succ s)·x = 2·(2^s·x)."""
    exps = _exp2(ts)
    g_pse = N.generalisation("Apsi", N.generalisation("Npsi",
        puissance_succ_eq_incond("Apsi", "Npsi")))
    pse = instancie(instancie(g_pse, DEUX), _t(ts))
    eq1 = N.modus_ponens(conjonction_intro(_card_deux(), fini_s), pse)  # 2^succ s = 2^s·2
    c1 = N.modus_ponens(eq1, congruence_terme(
        _exp2(successeur(_t(ts))), _prod(exps, DEUX), _prod(var("wdv"), _t(tx)), "wdv"))
    #   2^(succ s)·x = (2^s·2)·x
    comm = ops_produit_commutatif(exps, DEUX)                # 2^s·2 = 2·2^s
    c2 = N.modus_ponens(comm, congruence_terme(
        _prod(exps, DEUX), _prod(DEUX, exps), _prod(var("wdv"), _t(tx)), "wdv"))
    #   (2^s·2)·x = (2·2^s)·x
    c3 = ops_produit_associatif(DEUX, exps, _t(tx))          # (2·2^s)·x = 2·(2^s·x)
    return composer_egalites(composer_egalites(c1, c2), c3)


def _simplifier(ta, tb, tc, fa, fb, fc, nnc, eq_acbc):
    """de a·c = b·c (eq_acbc) : ⊢ a = b   (W2 ∀-clos aux termes)."""
    g = N.generalisation("asm", N.generalisation("bsm", N.generalisation(
        "csm", simplification_multiplicative("asm", "bsm", "csm"))))
    inst3 = instancie(instancie(instancie(g, _t(ta)), _t(tb)), _t(tc))
    conj = conjonction_intro(
        conjonction_intro(fa, conjonction_intro(fb, fc)),
        conjonction_intro(nnc, eq_acbc))
    return N.modus_ponens(conj, inst3)


def _pair_temoin(tx, tQ, eq_x_2Q, fini_Q):
    """de x = 2·Q et Fini Q : ⊢ est_pair_propre(x)   (S5 au témoin Q, lieur qdiv)."""
    corps = et(est_fini(var("qdiv")), egal(_t(tx), _prod(DEUX, var("qdiv"))))
    wit = conjonction_intro(fini_Q, eq_x_2Q)
    return N.modus_ponens(wit, N.s5(corps, _t(tQ), "qdiv"))


def _egal_neutre_20(tx, card_x):
    """{card_x ⊢ est_cardinal x} ⊢ x = 2^0·x   (neutre + 2^0=1 + commutation)."""
    vx = _t(tx)
    n1 = ops_produit_un_droite(vx, card_x)                   # x·1 = x
    s1 = N.modus_ponens(n1, symetrie(_prod(vx, UN), vx))     # x = x·1
    e0 = exposant_zero_un(DEUX)                              # 2^0 = 1
    un_eq_e0 = N.modus_ponens(e0, symetrie(_exp2(ZERO), UN))  # 1 = 2^0
    c1 = N.modus_ponens(un_eq_e0, congruence_terme(
        UN, _exp2(ZERO), _prod(vx, var("wdv")), "wdv"))             # x·1 = x·2^0
    c2 = ops_produit_commutatif(vx, _exp2(ZERO))             # x·2^0 = 2^0·x
    return composer_egalites(composer_egalites(s1, c1), c2)  # x = 2^0·x


# ══════════════════════════════════════════════════════════════════════════════
#  La récurrence C61 — deux_valuation_unique
# ══════════════════════════════════════════════════════════════════════════════
def _ANTE(b):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    vmp, vu, vup = var("mpv"), var("udv"), var("upv")
    return et(et(est_fini(vmp), et(est_fini(vu), est_fini(vup))),
              et(et(_impair(vu), _impair(vup)),
                 egal(_prod(_exp2(_t(b)), vu), _prod(_exp2(vmp), vup))))


def _CONC(b):
    return et(egal(_t(b), var("mpv")), egal(var("udv"), var("upv")))


def _P(b):
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import pourtout, impl
    return pourtout("mpv", pourtout("udv", pourtout("upv",
        impl(_ANTE(b), _CONC(b)))))


def _deballer(h):
    """Retourne (fmp, fu, fup, iu, iup, eq) depuis h ⊢ ANTE(b)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche as elg, conjonction_elim_droite as eld)
    A1, A2 = elg(h), eld(h)
    return (elg(A1), elg(eld(A1)), eld(eld(A1)),
            elg(elg(A2)), eld(elg(A2)), eld(A2))


# @livre Ch.III §6.3 Demo.Lem2 | E III.48 L.4-16 | PDF p.151  (unicité 2-adique — brique de l'injectivité du couplage)
def deux_valuation_unique(m="mdv", k="kdv"):
    """🎯 ⊢ Fini m ⇒ (∀mp)(∀u)(∀up)( (Fini mp ∧ Fini u ∧ Fini up ∧ impair u ∧
        impair up ∧ 2^m·u = 2^mp·up) ⇒ (m = mp ∧ u = up) ).

    Récurrence C61 sur m (patron pair_neq_impair) ; cas sur mp par tiers exclu :
    mp = 0 → neutre x·1=x et 2^0=1 ; mp = succ j → prédécesseur (Fini mp est une
    hypothèse du corps), Fini j (fini_successeur_implique_fini), doubleur
    2^(succ s)·x = 2·(2^s·x), simplification par 2 (W2), récurrence."""
    from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import impl
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
        conjonction_elim_gauche as elg, conjonction_elim_droite as eld,
        tiers_exclu, cas, equivalence_avant)
    from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
        existe_elimination)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
        est_cardinal, inf_strict_card)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (
        _ex_falso)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_successeur import (
        fini_successeur_implique_fini)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_deux import (
        fini_deux)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_aleph0 import (
        successeur_non_nul)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_recurrence_C61 import (
        _fini_et_P_implique_succ)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_principe_recurrence_preuve import (
        principe_recurrence_preuve, predecesseur_fini_universel)
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve)

    def _cut(thm, hyp, pr):
        return N.modus_ponens(pr, N.loi_deduction(hyp, thm))

    vmp, vu, vup = var("mpv"), var("udv"), var("upv")
    vkp = var("kpred")
    P = _P

    def _fini_k_de(b_eq, card_k, fmp):
        """{b_eq ⊢ mpv=succ k ; card_k ; fmp ⊢ Fini mpv} ⊢ Fini kpred."""
        leib = N.s6(vmp, successeur(vkp), "wfk", est_fini(var("wfk")))
        fini_succk = N.modus_ponens(fmp, equivalence_avant(N.modus_ponens(b_eq, leib)))
        fsif = instancie(N.generalisation("afsk",
            fini_successeur_implique_fini("afsk")), vkp)
        return N.modus_ponens(fini_succk, N.modus_ponens(card_k, fsif))

    def _corps_pred():
        return et(et(egal(vmp, successeur(vkp)), est_cardinal(vkp)),
                  inf_strict_card(vkp, vmp))

    # ── P[0] ──────────────────────────────────────────────────────────────────
    h0 = N.assume(_ANTE(ZERO))
    fmp, fu, fup, iu, iup, eq = _deballer(h0)
    card_u, card_up = elg(fu), elg(fup)
    te0 = tiers_exclu(egal(vmp, ZERO))
    #   A : mpv = 0
    ha = N.assume(egal(vmp, ZERO))
    cong_a = N.modus_ponens(ha, congruence_terme(
        vmp, ZERO, _prod(_exp2(var("wdv")), vup), "wdv"))           # 2^mpv·up = 2^0·up
    eq2 = composer_egalites(eq, cong_a)                      # 2^0·u = 2^0·up
    nu = _egal_neutre_20(vu, card_u)                         # u = 2^0·u
    nup = _egal_neutre_20(vup, card_up)                      # up = 2^0·up
    u_eq_up = composer_egalites(composer_egalites(nu, eq2),
        N.modus_ponens(nup, symetrie(vup, _prod(_exp2(ZERO), vup))))   # u = up
    m_eq = N.modus_ponens(ha, symetrie(vmp, ZERO))           # ZERO = mpv
    brA0 = N.loi_deduction(egal(vmp, ZERO),
                           conjonction_intro(m_eq, u_eq_up))
    #   B : mpv ≠ 0  →  droite paire, u pair, contredit impair u
    hb = N.assume(non(egal(vmp, ZERO)))
    pred = N.modus_ponens(conjonction_intro(fmp, hb),
                          instancie(predecesseur_fini_universel_preuve(), vmp))
    hK = N.assume(_corps_pred())
    b_eq = elg(elg(hK))                                      # mpv = succ k
    card_k = eld(elg(hK))
    fini_k = _fini_k_de(b_eq, card_k, fmp)
    cong_b = N.modus_ponens(b_eq, congruence_terme(
        vmp, successeur(vkp), _prod(_exp2(var("wdv")), vup), "wdv"))   # 2^mpv·up = 2^succk·up
    dbl = _double(vkp, vup, fini_k)                          # 2^succk·up = 2·(2^k·up)
    Q = _prod(_exp2(vkp), vup)
    eqP = composer_egalites(composer_egalites(eq, cong_b), dbl)   # 2^0·u = 2·Q
    u_eq_2Q = composer_egalites(_egal_neutre_20(vu, card_u), eqP)  # u = 2·Q
    pair_u = _pair_temoin(vu, Q, u_eq_2Q,
                          _fini_prod(_exp2(vkp), vup, _fini_exp(vkp, fini_k), fup))
    absurd0 = _ex_falso(pair_u, iu, _CONC(ZERO))
    exk = existe_elimination(N.loi_deduction(_corps_pred(), absurd0), "kpred")
    brB0 = N.loi_deduction(non(egal(vmp, ZERO)), N.modus_ponens(pred, exk))
    conc0 = cas(te0, brA0, brB0)
    p0 = N.generalisation("mpv", N.generalisation("udv", N.generalisation(
        "upv", N.loi_deduction(_ANTE(ZERO), conc0))))
    assert p0.conclusion == P(ZERO), "deux_valuation : P[0] mal formé"

    # ── pas : (Fini n et P[n]) ⇒ P[succ n] ────────────────────────────────────
    vn = var(m)
    h2 = N.assume(et(est_fini(vn), P(vn)))
    fn, Pn = elg(h2), eld(h2)
    hA = N.assume(_ANTE(successeur(vn)))
    fmp, fu, fup, iu, iup, eq = _deballer(hA)
    card_u, card_up = elg(fu), elg(fup)
    dblg = _double(vn, vu, fn)                               # 2^(succ n)·u = 2·(2^n·u)
    Qg = _prod(_exp2(vn), vu)
    te1 = tiers_exclu(egal(vmp, ZERO))
    #   A : mpv = 0  →  up = 2·Qg pair, contredit impair up
    ha1 = N.assume(egal(vmp, ZERO))
    cong_a1 = N.modus_ponens(ha1, congruence_terme(
        vmp, ZERO, _prod(_exp2(var("wdv")), vup), "wdv"))           # 2^mpv·up = 2^0·up
    #   up = 2^0·up = 2^mpv·up = 2^(succ n)·u = 2·Qg
    chaine = composer_egalites(composer_egalites(composer_egalites(
        _egal_neutre_20(vup, card_up),
        N.modus_ponens(cong_a1, symetrie(_prod(_exp2(vmp), vup),
                                         _prod(_exp2(ZERO), vup)))),
        N.modus_ponens(eq, symetrie(_prod(_exp2(successeur(vn)), vu),
                                    _prod(_exp2(vmp), vup)))),
        dblg)                                                # up = 2·Qg
    pair_up = _pair_temoin(vup, Qg, chaine,
                           _fini_prod(_exp2(vn), vu, _fini_exp(vn, fn), fu))
    absurd1 = _ex_falso(pair_up, iup, _CONC(successeur(vn)))
    brA1 = N.loi_deduction(egal(vmp, ZERO), absurd1)
    #   B : mpv = succ j  →  simplifier par 2, récurrence
    hb1 = N.assume(non(egal(vmp, ZERO)))
    pred1 = N.modus_ponens(conjonction_intro(fmp, hb1),
                           instancie(predecesseur_fini_universel_preuve(), vmp))
    hK1 = N.assume(_corps_pred())
    b_eq1 = elg(elg(hK1))                                    # mpv = succ j (j=kpred)
    card_j = eld(elg(hK1))
    fini_j = _fini_k_de(b_eq1, card_j, fmp)
    cong_b1 = N.modus_ponens(b_eq1, congruence_terme(
        vmp, successeur(vkp), _prod(_exp2(var("wdv")), vup), "wdv"))
    dbld = _double(vkp, vup, fini_j)                         # 2^succj·up = 2·(2^j·up)
    Qd = _prod(_exp2(vkp), vup)
    #   2·Qg = 2^(succ n)·u = 2^mpv·up = 2^succj·up = 2·Qd
    eq_2Q = composer_egalites(composer_egalites(composer_egalites(
        N.modus_ponens(dblg, symetrie(_prod(_exp2(successeur(vn)), vu),
                                      _prod(DEUX, Qg))), eq), cong_b1), dbld)
    #   commuter : Qg·2 = 2·Qg = 2·Qd = Qd·2
    cg = ops_produit_commutatif(Qg, DEUX)                    # Qg·2 = 2·Qg
    cd = ops_produit_commutatif(DEUX, Qd)                    # 2·Qd = Qd·2
    eq_c = composer_egalites(composer_egalites(cg, eq_2Q), cd)   # Qg·2 = Qd·2
    fQg = _fini_prod(_exp2(vn), vu, _fini_exp(vn, fn), fu)
    fQd = _fini_prod(_exp2(vkp), vup, _fini_exp(vkp, fini_j), fup)
    nn2 = successeur_non_nul(UN)                             # ¬(DEUX = 0)
    eq_QgQd = _simplifier(Qg, Qd, DEUX, fQg, fQd, fini_deux(), nn2, eq_c)
    #   récurrence P[n] à (kpred, u, up)
    Pn_inst = instancie(instancie(instancie(Pn, vkp), vu), vup)
    ante_n = conjonction_intro(
        conjonction_intro(fini_j, conjonction_intro(fu, fup)),
        conjonction_intro(conjonction_intro(iu, iup), eq_QgQd))
    rec = N.modus_ponens(ante_n, Pn_inst)                    # n = j  et  u = up
    n_eq_j, u_eq_up1 = elg(rec), eld(rec)
    cong_s = N.modus_ponens(n_eq_j, congruence_terme(
        vn, vkp, successeur(var("wdv")), "wdv"))                    # succ n = succ j
    m_eq1 = composer_egalites(cong_s,
        N.modus_ponens(b_eq1, symetrie(vmp, successeur(vkp))))   # succ n = mpv
    concB = conjonction_intro(m_eq1, u_eq_up1)
    exk1 = existe_elimination(N.loi_deduction(_corps_pred(), concB), "kpred")
    brB1 = N.loi_deduction(non(egal(vmp, ZERO)), N.modus_ponens(pred1, exk1))
    conc1 = cas(te1, brA1, brB1)
    corps_pas = N.generalisation("mpv", N.generalisation("udv", N.generalisation(
        "upv", N.loi_deduction(_ANTE(successeur(vn)), conc1))))
    step = N.generalisation(m, N.loi_deduction(et(est_fini(vn), P(vn)), corps_pas))
    assert step.conclusion == _fini_et_P_implique_succ(P, m), \
        "deux_valuation : pas mal formé"

    # ── assemblage C61 ────────────────────────────────────────────────────────
    princ = principe_recurrence_preuve(P, m, k=k)
    pfu = predecesseur_fini_universel(k=k)
    if pfu in princ.hypotheses:
        princ = _cut(princ, pfu, predecesseur_fini_universel_preuve(k=k))
    fini_implique_P = N.modus_ponens(conjonction_intro(p0, step), princ)
    res = instancie(fini_implique_P, vn)                     # Fini m ⇒ P[m]
    assert not res.hypotheses, "deux_valuation_unique : hypothèses résiduelles"
    return res


__all__ = ["exposant_zero_un", "ops_produit_un_droite", "deux_valuation_unique"]
