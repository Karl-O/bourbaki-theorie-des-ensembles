# -*- coding: utf-8 -*-
"""DIVISEUR COMMUN DE a ET succ a — la brique H (Euclide-infinitude, la dure).

    ⊢ (Fini a ∧ card d ∧ ¬(d=0) ∧ d|a ∧ d|succ a) ⇒ d = 1                [H]

Le cœur : succ(a) EST LITTÉRALEMENT somme(a, {∅}) (déf. du successeur —
aucun pas de preuve). Sous témoins w1 (a = d·w1) et w2 (succ a = d·w2),
comparabilité(w2, w1) :
  A  w2 ≤ w1 : monotonie droite (niveau ENSEMBLES, pont Card = motif borne)
     ⇒ succ a ≤ a — mort (succ_pas_inf_egal).
  B  w1 ≤ w2, tiers-exclu sur w1 = w2 :
     B1 égaux  : a = succ a — mort (fini_implique_distinct_successeur).
     B2 ≠, comparabilité(succ w1, w2) :
        B2a succ w1 ≤ w2 : monotonie + produit_succ_distribue + Leibniz
            ⇒ a + d ≤ succ a ;
        B2b w2 ≤ succ w1 : successeur_ordre scinde — w2 ≤ w1 (antisymétrie
            ⇒ w1 = w2, mort) ou w2 = succ w1 (égalité ⇒ a + d ≤ succ a).
  QUEUE commune : succ a = somme(a, UN) (somme_cardinale_bien_definie +
  Eq({∅},1)) ⇒ a+d ≤ a+UN ⇒ d ≤ UN (additive_order_cancel) ; UN ≤ d
  (¬(d=∅) micro-preuve + un_inf_egal + pont Card({∅})=UN) ; antisymétrie."""
from __future__ import annotations

import sys
from pathlib import Path

_V9 = Path(__file__).resolve().parents[4]
if str(_V9) not in sys.path:
    sys.path.insert(0, str(_V9))

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (  # noqa: E402
    var, egal, et, impl, non,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import (  # noqa: E402
    noyau_abrege as N,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (  # noqa: E402
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie, cas, tiers_exclu,
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
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (  # noqa: E402
    somme_cardinale_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (  # noqa: E402
    est_cardinal, cardinal, inf_egal_card,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (  # noqa: E402
    _antisym_t, _inf_egal_transitive_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (  # noqa: E402
    equipotent_son_cardinal, inf_egal_reflexif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import (  # noqa: E402
    equipotence_symetrique,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_props_diverses import (  # noqa: E402
    equipotents_mutuellement_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_cardinaux_un_borne import (  # noqa: E402
    un_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.ordre_cardinaux.ensembles_sup_cardinal import (  # noqa: E402
    comparabilite_cardinaux_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.props_restantes.ensembles_divisibilite_propre import (  # noqa: E402
    divise_propre, _card_de_card_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_2_monotonie.ensembles_arith_cardinale_props_produit_monotone import (  # noqa: E402
    inf_egal_produit_droite,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (  # noqa: E402
    produit_cardinal_binaire,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (  # noqa: E402
    somme_cardinale_bien_definie,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import (  # noqa: E402
    est_fini, est_entier, successeur, UN, ZERO,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import (  # noqa: E402
    fini_implique_distinct_successeur, fini_implique_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_fini_un import (  # noqa: E402
    un_egale_card_singleton, eq_un_singleton, un_est_un_cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_prop3_produit_entier_iii5 import (  # noqa: E402
    produit_succ_distribue,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_prop4_surj_iii5 import (  # noqa: E402
    additive_order_cancel,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_successeur_ordre import (  # noqa: E402
    successeur_ordre, succ_pas_inf_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_1_n_objet_existence.ensembles_N_collectivise import (  # noqa: E402
    zero_inf_egal_cardinal,  # noqa: F401  (garde d'import homogène — non utilisé)
)
from outils_ia.arithmetique.machine_num import ex_falso, neg_intro  # noqa: E402

mp = N.modus_ponens
_SING = E.singleton(E.VIDE)


def _gen1_t(builder, nom, t):
    return instancie(N.generalisation(nom, builder(nom)), t)


def _gen2_t(builder, n1, n2, t1, t2):
    g = N.generalisation(n1, N.generalisation(n2, builder(n1, n2)))
    return instancie(instancie(g, t1), t2)


def _fic_t(t):
    return _gen1_t(fini_implique_cardinal, "AficH", t)


def _mut_t(tx, ty):
    """⊢ Eq(X,Y) ⇒ (X≤Y ∧ Y≤X)  (termes)."""
    return _gen2_t(equipotents_mutuellement_inf_egal, "XmuH", "YmuH", tx, ty)


def _pdroite_t(tb, tb1, tc):
    """⊢ (B ≤ B₁) ⇒ (C×B ≤ C×B₁)  (termes, niveau ensembles)."""
    g = inf_egal_produit_droite("BpdH", "B1pdH", "CpdH")
    gen = N.generalisation("BpdH", N.generalisation("B1pdH",
          N.generalisation("CpdH", g)))
    return instancie(instancie(instancie(gen, tb), tb1), tc)


def _card_le_card(le_set, tx, ty):
    """De ⊢ X ≤ Y (ensembles), ⊢ Card X ≤ Card Y  (pont borne : Eq + 2 trans)."""
    both_x = mp(_gen1_t(equipotent_son_cardinal, "XescH", tx),
                _mut_t(tx, cardinal(tx)))
    card_le_x = conjonction_elim_droite(both_x)              # Card X ≤ X
    both_y = mp(_gen1_t(equipotent_son_cardinal, "XescH", ty),
                _mut_t(ty, cardinal(ty)))
    y_le_card = conjonction_elim_gauche(both_y)              # Y ≤ Card Y
    t1 = mp(conjonction_intro(card_le_x, le_set),
            _inf_egal_transitive_t(cardinal(tx), tx, ty))
    return mp(conjonction_intro(t1, y_le_card),
              _inf_egal_transitive_t(cardinal(tx), ty, cardinal(ty)))


def _rw_avant(eq_thm, motif_w, w, thm):
    """De ⊢ x=y, ⊢ F(x) : ⊢ F(y)   (s6 + équivalence avant)."""
    x, y = eq_thm.conclusion.termes
    return mp(thm, equivalence_avant(mp(eq_thm, N.s6(x, y, w, motif_w))))


def _rw_arriere(eq_thm, motif_w, w, thm):
    """De ⊢ x=y, ⊢ F(y) : ⊢ F(x)   (s6 + équivalence arrière)."""
    x, y = eq_thm.conclusion.termes
    return mp(thm, equivalence_arriere(mp(eq_thm, N.s6(x, y, w, motif_w))))


def diviseur_commun_succ_cible(a="aH", d="dH", w1="w1H", w2="w2H"):
    """Énoncé visé : (Fini a ∧ card d ∧ ¬(d=0) ∧ d|a ∧ d|succ a) ⇒ d = 1."""
    va, vd = var(a), var(d)
    return impl(et(et(et(est_fini(va), est_cardinal(vd)), non(egal(vd, ZERO))),
                   et(divise_propre(vd, va, q=w1),
                      divise_propre(vd, successeur(va), q=w2))),
                egal(vd, UN))


def diviseur_commun_succ(a="aH", d="dH", w1="w1H", w2="w2H"):
    """🎯 ⊢ (Fini a ∧ card d ∧ d≠0 ∧ d|a ∧ d|succ a) ⇒ d = 1.            [H]"""
    va, vd, vw1, vw2 = var(a), var(d), var(w1), var(w2)
    sa = successeur(va)
    assert sa == somme_cardinale_binaire(va, _SING), "succ ≠ somme(·,{∅}) ?!"
    H = et(et(et(est_fini(va), est_cardinal(vd)), non(egal(vd, ZERO))),
           et(divise_propre(vd, va, q=w1), divise_propre(vd, sa, q=w2)))
    h = N.assume(H)
    h_fa = conjonction_elim_gauche(conjonction_elim_gauche(
        conjonction_elim_gauche(h)))                         # Fini a
    h_cd = conjonction_elim_droite(conjonction_elim_gauche(
        conjonction_elim_gauche(h)))                         # card d
    h_n0 = conjonction_elim_droite(conjonction_elim_gauche(h))   # ¬(d=0)
    h_d1 = conjonction_elim_gauche(conjonction_elim_droite(h))   # d|a
    h_d2 = conjonction_elim_droite(conjonction_elim_droite(h))   # d|succ a
    card_d_eq = mp(h_cd, _card_de_card_t(vd))                # Card d = d
    cible = egal(vd, UN)

    # ── UN ≤ d  (ambiant : d ≠ ∅ par micro-preuve, {∅}≤d, pont Card) ────────
    hv = N.assume(egal(vd, E.VIDE))
    trou = var("wtrouH")
    cgv = mp(hv, congruence_terme(vd, E.VIDE, cardinal(trou), w="wtrouH"))
    assert cgv.conclusion == egal(cardinal(vd), ZERO)        # Card d = Card ∅ = 0
    d_eq_0 = composer_egalites(mp(card_d_eq, symetrie(cardinal(vd), vd)), cgv)
    assert d_eq_0.conclusion == egal(vd, ZERO)
    n_vide = neg_intro(egal(vd, E.VIDE),
                       ex_falso(d_eq_0, h_n0, non(egal(vd, E.VIDE))))
    sing_le_d = mp(n_vide, _gen1_t(un_inf_egal, "XuiH", vd))     # {∅} ≤ d
    both_s = mp(_gen1_t(equipotent_son_cardinal, "XescH", _SING),
                _mut_t(_SING, cardinal(_SING)))
    cs_le_s = conjonction_elim_droite(both_s)                # Card{∅} ≤ {∅}
    cs_le_d = mp(conjonction_intro(cs_le_s, sing_le_d),
                 _inf_egal_transitive_t(cardinal(_SING), _SING, vd))
    ues = un_egale_card_singleton()                          # 1 = Card({∅})
    assert ues.conclusion == egal(UN, cardinal(_SING))
    un_le_d = _rw_arriere(ues, inf_egal_card(var("wH1"), vd), "wH1", cs_le_d)
    assert un_le_d.conclusion == inf_egal_card(UN, vd)       # 1 ≤ d

    # ── corridor sous témoins w1, w2 ────────────────────────────────────────
    m1 = et(est_fini(vw1), egal(va, produit_cardinal_binaire(vd, vw1)))
    m2 = et(est_fini(vw2), egal(sa, produit_cardinal_binaire(vd, vw2)))
    t1_ = N.assume(m1)
    t2_ = N.assume(m2)
    fin1, eq1 = conjonction_elim_gauche(t1_), conjonction_elim_droite(t1_)
    fin2, eq2 = conjonction_elim_gauche(t2_), conjonction_elim_droite(t2_)
    card_w1 = mp(fin1, _fic_t(vw1))
    card_w2 = mp(fin2, _fic_t(vw2))
    pd_w1 = produit_cardinal_binaire(vd, vw1)
    pd_w2 = produit_cardinal_binaire(vd, vw2)
    somme_ad = somme_cardinale_binaire(va, vd)

    # queue commune : de ⊢ a+d ≤ succ a, conclure d = 1
    def _queue(le_sad):
        eq_rs = mp(conjonction_intro(_eq_refl_a(), _eq_sym_sing_un()),
                   _sbd_t())                                 # succ a = a+1
        assert eq_rs.conclusion == egal(sa, somme_cardinale_binaire(va, UN))
        le_ss = _rw_avant(eq_rs, inf_egal_card(somme_ad, var("wHT")), "wHT",
                          le_sad)                            # a+d ≤ a+UN
        aoc = _aoc_t(va, vd, UN)
        assert est_entier(va) == est_fini(va), "est_entier ≠ est_fini ?!"
        d_le_un = mp(conjonction_intro(conjonction_intro(
            conjonction_intro(h_fa, h_cd), un_est_un_cardinal()), le_ss), aoc)
        assert d_le_un.conclusion == inf_egal_card(vd, UN)
        return mp(conjonction_intro(conjonction_intro(
            conjonction_intro(d_le_un, un_le_d), h_cd), un_est_un_cardinal()),
            _antisym_t(vd, UN))                              # d = 1

    def _eq_refl_a():
        from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence import (
            equipotence_reflexive_t,
        )
        return equipotence_reflexive_t(va)                   # Eq(a, a)

    def _eq_sym_sing_un():
        # lieur de graphe CANONIQUE « F » (celui d'equipotent — mesuré sur
        # eq_un_singleton : un lieur exotique casse le modus ponens)
        sym_all = N.generalisation("XsyH", N.generalisation("YsyH",
            equipotence_symetrique("F", "XsyH", "YsyH")))
        g = instancie(instancie(sym_all, UN), _SING)
        return mp(eq_un_singleton(), g)                      # Eq({∅}, 1)

    def _sbd_t():
        g = somme_cardinale_bien_definie("AsbH", "BsbH", "A1sbH", "B1sbH")
        gen = N.generalisation("AsbH", N.generalisation("BsbH",
              N.generalisation("A1sbH", N.generalisation("B1sbH", g))))
        return instancie(instancie(instancie(instancie(gen, va), _SING),
                                   va), UN)

    def _aoc_t(ta, tu, tv):
        g = N.generalisation("aocH", N.generalisation("uocH",
            N.generalisation("vocH", additive_order_cancel("aocH", "uocH",
                                                           "vocH"))))
        return instancie(instancie(instancie(g, ta), tu), tv)

    # ── branche A : w2 ≤ w1 → succ a ≤ a → mort ─────────────────────────────
    hA = N.assume(inf_egal_card(vw2, vw1))
    le_setA = mp(hA, _pdroite_t(vw2, vw1, vd))
    le_cardA = _card_le_card(le_setA, E.produit(vd, vw2), E.produit(vd, vw1))
    assert le_cardA.conclusion == inf_egal_card(pd_w2, pd_w1)
    sA1 = _rw_arriere(eq2, inf_egal_card(var("wHA"), pd_w1), "wHA", le_cardA)
    sA2 = _rw_arriere(eq1, inf_egal_card(sa, var("wHA2")), "wHA2", sA1)
    assert sA2.conclusion == inf_egal_card(sa, va)           # succ a ≤ a
    spie = mp(h_fa, _gen1_t(succ_pas_inf_egal, "BspH", va))  # ¬(succ a ≤ a)
    brA = N.loi_deduction(inf_egal_card(vw2, vw1), ex_falso(sA2, spie, cible))

    # ── branche B : w1 ≤ w2, tiers-exclu sur w1 = w2 ────────────────────────
    hB = N.assume(inf_egal_card(vw1, vw2))

    # B1 : w1 = w2 → a = succ a → mort
    hEq = N.assume(egal(vw1, vw2))
    cgB1 = mp(hEq, congruence_terme(vw1, vw2,
                                    produit_cardinal_binaire(vd, trou),
                                    w="wtrouH"))             # d·w1 = d·w2
    a_eq_sa = composer_egalites(composer_egalites(eq1, cgB1),
                                mp(eq2, symetrie(sa, pd_w2)))
    assert a_eq_sa.conclusion == egal(va, sa)
    fds = mp(h_fa, _gen1_t(fini_implique_distinct_successeur, "AfdH", va))
    brB1 = N.loi_deduction(egal(vw1, vw2), ex_falso(a_eq_sa, fds, cible))

    # B2 : w1 ≠ w2 → comparabilité(succ w1, w2)
    hNe = N.assume(non(egal(vw1, vw2)))
    le_target = inf_egal_card(somme_ad, sa)                  # a+d ≤ succ a
    psd = mp(conjonction_intro(h_cd, card_w1),
             produit_succ_distribue(vd, vw1))                # d·(w1+1) = d·w1 + d
    eq_dsw1 = psd.conclusion
    assert eq_dsw1 == egal(produit_cardinal_binaire(vd, successeur(vw1)),
                           somme_cardinale_binaire(pd_w1, vd))
    eq1s = mp(eq1, symetrie(va, pd_w1))                      # d·w1 = a → non, a=d·w1 sym
    cg_sad = mp(eq1s, congruence_terme(pd_w1, va,
                                       somme_cardinale_binaire(trou, vd),
                                       w="wtrouH"))          # d·w1 + d = a + d
    # B2a : succ w1 ≤ w2 → monotonie → a+d ≤ succ a
    hle = N.assume(inf_egal_card(successeur(vw1), vw2))
    le_setB = mp(hle, _pdroite_t(successeur(vw1), vw2, vd))
    le_cardB = _card_le_card(le_setB, E.produit(vd, successeur(vw1)),
                             E.produit(vd, vw2))
    sB1 = _rw_arriere(eq2, inf_egal_card(produit_cardinal_binaire(
        vd, successeur(vw1)), var("wHB")), "wHB", le_cardB)  # d·(w1+1) ≤ succ a
    sB2 = _rw_avant(psd, inf_egal_card(var("wHB2"), sa), "wHB2", sB1)
    sB3 = _rw_avant(cg_sad, inf_egal_card(var("wHB3"), sa), "wHB3", sB2)
    assert sB3.conclusion == le_target
    brB2a = N.loi_deduction(inf_egal_card(successeur(vw1), vw2), sB3)

    # B2b : w2 ≤ succ w1 → successeur_ordre scinde
    hge = N.assume(inf_egal_card(vw2, successeur(vw1)))
    eqvB = mp(card_w2, _gen2_t(successeur_ordre, "XsoH", "BsoH", vw2, vw1))
    disjB = mp(hge, conjonction_elim_gauche(eqvB))           # w2≤w1 ∨ w2=succ w1
    #   w2 ≤ w1 : avec w1 ≤ w2, antisymétrie ⇒ w1 = w2 — mort contre hNe
    hc1 = N.assume(inf_egal_card(vw2, vw1))
    w_eq = mp(conjonction_intro(conjonction_intro(
        conjonction_intro(hB, hc1), card_w1), card_w2), _antisym_t(vw1, vw2))
    brC1 = N.loi_deduction(inf_egal_card(vw2, vw1),
                           ex_falso(w_eq, hNe, le_target))
    #   w2 = succ w1 : égalité en chaîne ⇒ a+d = succ a ⇒ ≤ par réflexivité
    hc2 = N.assume(egal(vw2, successeur(vw1)))
    cgC2 = mp(hc2, congruence_terme(vw2, successeur(vw1),
                                    produit_cardinal_binaire(vd, trou),
                                    w="wtrouH"))             # d·w2 = d·(w1+1)
    sa_eq = composer_egalites(composer_egalites(composer_egalites(
        eq2, cgC2), psd), cg_sad)                            # succ a = a + d
    assert sa_eq.conclusion == egal(sa, somme_ad)
    refl_le = _gen1_t(inf_egal_reflexif, "XrlH", somme_ad)   # a+d ≤ a+d
    le_c2 = _rw_avant(mp(sa_eq, symetrie(sa, somme_ad)),
                      inf_egal_card(somme_ad, var("wHC")), "wHC", refl_le)
    assert le_c2.conclusion == le_target
    brC2 = N.loi_deduction(egal(vw2, successeur(vw1)), le_c2)
    brB2b = N.loi_deduction(inf_egal_card(vw2, successeur(vw1)),
                            cas(disjB, brC1, brC2))

    compar2 = comparabilite_cardinaux_terme(successeur(vw1), vw2)
    assert compar2.conclusion.tag == "ou"
    le_sad = cas(compar2, brB2a, brB2b)                      # a+d ≤ succ a
    d_eq_un_B2 = _queue(le_sad)                              # d = 1
    brB2 = N.loi_deduction(non(egal(vw1, vw2)), d_eq_un_B2)
    rB = cas(tiers_exclu(egal(vw1, vw2)), brB1, brB2)
    brB = N.loi_deduction(inf_egal_card(vw1, vw2), rB)

    compar = comparabilite_cardinaux_terme(vw2, vw1)
    assert compar.conclusion.tag == "ou"
    r = cas(compar, brA, brB)                                # d = 1  [m1, m2, H]
    assert r.conclusion == cible

    # ── double ∃-élimination puis décharge ──────────────────────────────────
    r2 = mp(h_d2, existe_elimination(N.loi_deduction(m2, r), w2))
    r1 = mp(h_d1, existe_elimination(N.loi_deduction(m1, r2), w1))
    th = N.loi_deduction(H, r1)
    assert th.est_clos and not th.hypotheses, "diviseur_commun_succ non clos"
    assert th.conclusion == diviseur_commun_succ_cible(a, d, w1, w2), (
        "diviseur_commun_succ : conclusion != cible")
    return th


__all__ = ["diviseur_commun_succ", "diviseur_commun_succ_cible"]
