"""§III.6 (prérequis Lemme 2, ℵ₀·ℵ₀=ℵ₀) — arithmétique multiplicative de ℕ vers
l'injection de couplage  (m,n) ↦ 2^m·3^n  :  ℕ×ℕ ↪ ℕ.

Construit bottom-up (cf. PLAN) :
  1. puissance_succ_eq_incond ⊢ (card a et Fini n) ⇒ a^(n+1) = a^n · a   (INCONDITIONNEL,
     hyp (B) de support déchargée par `B_preuve`, instance du keystone CLOS
     `eq_exposant_invariant`, exactement comme `puissance_entiers_ferme_inconditionnel`) ;
  2. trois_puiss_impair ⊢ Fini n ⇒ est_impair_propre(3^n)   (3^n impair, récurrence) ;
  3. deux_puiss_pair ⊢ (Fini k et k≠0) ⇒ est_pair_propre(2^k)   (2^k pair pour k≥1) ;
  4. puissance_strict_croissante ⊢ (Fini m et Fini m' et m<m') ⇒ 3^m < 3^m'  (⇒ injective).

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, ou, non, impl, existe, pourtout
from bourbaki.logique import noyau_abrege as N
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere,
)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal, inf_strict_card
from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.entiers.ensembles_entiers import est_fini, est_entier, successeur, ZERO, DEUX, TROIS


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


# ══════════════════════════════════════════════════════════════════════════════
#  (1)  a^(n+1) = a^n · a   INCONDITIONNEL
# ══════════════════════════════════════════════════════════════════════════════
def puissance_succ_eq_incond_cible(a="Apsi", n="Npsi"):
    va, vn = _t(a), _t(n)
    an = exposant_cardinal_binaire(va, vn)
    lhs = exposant_cardinal_binaire(va, successeur(vn))
    rhs = produit_cardinal_binaire(an, va)
    return impl(et(est_cardinal(va), est_fini(vn)), egal(lhs, rhs))


def puissance_succ_eq_incond(a="Apsi", n="Npsi"):
    """🎯 ⊢ (est_cardinal a et Fini n) ⇒ a^(n+1) = a^n · a.   (INCONDITIONNEL.)

    `puissance_succ_eq(a,n)` ⊢ (B) ⇒ ((card a et card n) ⇒ a^(n+1)=a^n·a) ;
    `B_preuve(a,n)` (instance CLOSE du keystone `eq_exposant_invariant`) décharge (B) ;
    `est_fini n` fournit `est_cardinal n` (1er conjoint).  theorie=22."""
    from bourbaki.cardinaux.ensembles_n_arith_iii5 import (
        puissance_succ_eq, exposant_invariance_enonce,
    )
    from bourbaki.cardinaux.ensembles_puissance_entiers_inconditionnel import B_preuve
    va, vn = _t(a), _t(n)

    pse = puissance_succ_eq(va, vn)        # (B) ⇒ ((card a et card n) ⇒ a^(n+1)=a^n·a)
    B = B_preuve(va, vn)                    # ⊢ (B)  CLOS
    assert B.conclusion == exposant_invariance_enonce(va, vn), "B_preuve : forme ≠ (B)"
    sous_card = N.modus_ponens(B, pse)     # (card a et card n) ⇒ a^(n+1)=a^n·a

    h = N.assume(et(est_cardinal(va), est_fini(vn)))
    ca = conjonction_elim_gauche(h)        # est_cardinal a
    fn = conjonction_elim_droite(h)        # Fini n
    cn = conjonction_elim_gauche(fn)       # est_cardinal n
    eq = N.modus_ponens(conjonction_intro(ca, cn), sous_card)   # a^(n+1)=a^n·a
    out = N.loi_deduction(et(est_cardinal(va), est_fini(vn)), eq)
    assert out.conclusion == puissance_succ_eq_incond_cible(a, n), \
        f"puissance_succ_eq_incond : conclusion inattendue\n{out.conclusion}"
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  outils communs
# ══════════════════════════════════════════════════════════════════════════════
def _psi_base_t(ta, n):
    """`puissance_succ_eq_incond` CAPTURE-SAFE en la BASE :
       ⊢ (est_cardinal a et Fini n) ⇒ a^(n+1)=a^n·a, pour une base TERME `ta` (littéral
       composé comme TROIS/DEUX), l'exposant `n` restant une VARIABLE de récurrence.

    `prop9_close` (appelé par `puissance_succ_eq`) contient des graphes-témoins internes
    (`graphe_terme_fonctionnel`) dont les liants CAPTURENT une base littérale τ-imbriquée
    → on prouve sur le NOM FRAIS « Apsibase » puis généralisation+instanciation au TERME."""
    vn = _t(n)
    base_thm = puissance_succ_eq_incond("Apsibase", vn)   # sur nom frais
    gen = N.generalisation("Apsibase", base_thm)
    return instancie(gen, _t(ta))


def _congr_succ(eq_thm):
    """De ⊢ (u = v) déduit ⊢ ( successeur(u) = successeur(v) )."""
    u, v = eq_thm.conclusion.termes
    leib = N.s6(u, v, "wcs3", egal(successeur(u), successeur(var("wcs3"))))
    eqv = N.modus_ponens(eq_thm, leib)
    refl = N.reflexivite(successeur(u))
    return N.modus_ponens(refl, equivalence_avant(eqv))


def _card_est_cardinal_t(tX):
    """⊢ est_cardinal(Card X)  (version TERME)."""
    from bourbaki.entiers.ensembles_entiers_theoremes import card_est_un_cardinal
    gen = N.generalisation("Xcuc3", card_est_un_cardinal("Xcuc3", lieur="X"))
    return instancie(gen, _t(tX))


def _exposant_est_cardinal(ta, tb):
    """⊢ est_cardinal(a^b)  (a^b = Card(𝓕(b;a)) est un cardinal)."""
    return _card_est_cardinal_t(E.applications(_t(tb), _t(ta)))


# ══════════════════════════════════════════════════════════════════════════════
#  3 EST IMPAIR  —  est_impair_propre(3)
# ══════════════════════════════════════════════════════════════════════════════
def trois_impair():
    """🎯 ⊢ est_impair_propre(3).   ( ¬(2 | 3). )

    3 = succ(2) = succ(2·1)  (2·1 = 2 via deux_succ_eq(0)).  deux_k_plus_un_impair(1)
    ⊢ Fini 1 ⇒ impair(succ(2·1)) ; Fini 1 ; Leibniz succ(2·1)=3 ⇒ impair(3)."""
    from bourbaki.cardinaux.ensembles_parite_iii5 import (
        deux_k_plus_un_impair, deux_fois, deux_succ_eq, _deux_fois_zero_eq,
    )
    from bourbaki.cardinaux.ensembles_divisibilite_propre import est_impair_propre
    from bourbaki.entiers.ensembles_entiers import UN
    from bourbaki.entiers.ensembles_fini_zero import zero_est_un_cardinal, fini_zero
    from bourbaki.entiers.ensembles_fini_un import fini_un

    # 2·1 = 2 :  deux_succ_eq(0) : card 0 ⇒ 2·(0+1) = succ(succ(2·0))
    #   0+1 = succ(0) = UN (literal) ; 2·0 = 0 ; succ(succ(0)) = succ(1) = 2 = DEUX (literal).
    dse0 = N.modus_ponens(zero_est_un_cardinal(), deux_succ_eq(ZERO))  # 2·(0+1)=succ(succ(2·0))
    eq20 = _deux_fois_zero_eq()                          # 2·0 = 0
    # succ(succ(2·0)) = succ(succ(0)) = DEUX  (2 successeurs de l'égalité 2·0=0)
    ss = _congr_succ(_congr_succ(eq20))                  # succ(succ(2·0)) = succ(succ(0)) = DEUX
    twoUN_eq_DEUX = composer_egalites(dse0, ss)          # 2·1 = DEUX  (2·(0+1)=2·UN literal)
    # impair(succ(2·1)) via deux_k_plus_un_impair(1), Fini 1
    dki = N.modus_ponens(fini_un(), deux_k_plus_un_impair(UN))   # impair(succ(2·1))
    # succ(2·1) = succ(2) = 3 = TROIS
    succ_eq = _congr_succ(twoUN_eq_DEUX)                 # succ(2·1) = succ(2) = TROIS
    leib = N.modus_ponens(succ_eq,
        N.s6(successeur(deux_fois(UN)), TROIS, "wti", est_impair_propre(var("wti"))))
    res = N.modus_ponens(dki, equivalence_avant(leib))   # impair(3)
    assert res.conclusion == est_impair_propre(TROIS), \
        f"trois_impair : conclusion inattendue\n{res.conclusion}"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (2)  3^n EST IMPAIR  —  Fini n ⇒ est_impair_propre(3^n)   (récurrence sur n)
# ══════════════════════════════════════════════════════════════════════════════
def _P_trois_impair(n):
    from bourbaki.cardinaux.ensembles_divisibilite_propre import est_impair_propre
    return est_impair_propre(exposant_cardinal_binaire(TROIS, _t(n)))


def trois_puiss_impair_cible(n="ntpi"):
    return impl(est_fini(_t(n)), _P_trois_impair(n))


def _trois_puiss_impair_P0():
    """⊢ est_impair_propre(3^0).   (3^0 = Card({∅}) = 1 ; impair(1) = un_impair.)"""
    from bourbaki.cardinaux.arithmetique.ensembles_exposant_cardinal import (
        exposant_cardinal_zero_egale_un,
    )
    from bourbaki.cardinaux.ensembles_parite_iii5 import un_impair
    from bourbaki.cardinaux.ensembles_divisibilite_propre import est_impair_propre
    from bourbaki.entiers.ensembles_fini_un import un_egale_card_singleton
    from bourbaki.entiers.ensembles_fini_zero import cardinal_vide_egale_vide
    from bourbaki.entiers.ensembles_entiers import UN
    # CIBLE : impair( Card(𝓕(ZERO; 3)) )  où ZERO = Card(∅) (≠ ∅ structurellement).
    # `exposant_cardinal_zero_egale_un` donne Card(𝓕(∅; 3)) = Card({∅}) (exposant ∅).
    # On PONTE ZERO → ∅ par `cardinal_vide_egale_vide` (⊢ Card(∅)=∅, i.e. ZERO=∅) +
    # Leibniz sur le slot EXPOSANT de Card(applications(•, 3)).
    exp_ZERO = exposant_cardinal_binaire(TROIS, ZERO)    # Card(𝓕(ZERO;3))  (cible récurrence)
    exp_VIDE = cardinal(E.applications(E.VIDE, TROIS))   # Card(𝓕(∅;3))
    cve = cardinal_vide_egale_vide()                     # Card(∅) = ∅   (= ZERO = ∅)
    # Card(𝓕(ZERO;3)) = Card(𝓕(∅;3))  : Leibniz ZERO→∅ dans cardinal(applications(•,3))
    leib_expo = N.modus_ponens(cve,
        N.s6(ZERO, E.VIDE, "wexp0",
             egal(exp_ZERO, cardinal(E.applications(var("wexp0"), TROIS)))))
    # (réflexivité Card(𝓕(ZERO;3))=Card(𝓕(ZERO;3)) ⇒, via équiv, =Card(𝓕(∅;3)))
    eqZV = N.modus_ponens(N.reflexivite(exp_ZERO), equivalence_avant(leib_expo))  # =exp_VIDE
    # 3^0(∅) = Card({∅})  — capture-safe (TROIS littéral composé : τ-capture)
    eqz = instancie(
        N.generalisation("Atpz0", exposant_cardinal_zero_egale_un(var("Atpz0"))),
        TROIS)                                            # Card(𝓕(∅;3)) = Card({∅})
    un_eq = un_egale_card_singleton()                    # 1 = Card({∅})
    card_sing_eq_un = N.modus_ponens(un_eq, symetrie(UN, cardinal(E.singleton(E.VIDE))))  # Card({∅})=1
    # Card(𝓕(ZERO;3)) = Card(𝓕(∅;3)) = Card({∅}) = 1
    exp30_eq_un = composer_egalites(composer_egalites(eqZV, eqz), card_sing_eq_un)   # 3^0 = 1
    imp1 = un_impair()                                   # impair(1)
    # transport 1 → 3^0 : impair(1) ⇒ impair(Card(𝓕(ZERO;3)))  (1 = 3^0)
    un_eq_exp = N.modus_ponens(exp30_eq_un, symetrie(exp_ZERO, UN))  # 1 = 3^0
    leib = N.modus_ponens(un_eq_exp,
        N.s6(UN, exp_ZERO, "wtp0", est_impair_propre(var("wtp0"))))
    res = N.modus_ponens(imp1, equivalence_avant(leib))  # impair(Card(𝓕(ZERO;3)))
    assert res.conclusion == _P_trois_impair(ZERO), \
        f"P0 trois_impair mal formé\n{res.conclusion}\n{_P_trois_impair(ZERO)}"
    return res


def _trois_puiss_impair_step(n="ntpis"):
    """⊢ (∀n)( (Fini n et P[n]) ⇒ P[n+1] ),  P[n]=impair(3^n).

    3^(n+1)=3^n·3 (step1, card 3^n et Fini n) ; 3 impair (trois_impair) ; impair·impair
    impair (impair_fois_impair, Fini 3^n, Fini 3) ; Leibniz 3^n·3 → 3^(n+1)."""
    from bourbaki.cardinaux.ensembles_parite_iii5 import impair_fois_impair
    from bourbaki.cardinaux.ensembles_divisibilite_propre import est_impair_propre
    from bourbaki.cardinaux.ensembles_puissance_deux_trois_NN import trois_puissance_dans_NN
    from bourbaki.entiers.ensembles_fini_trois_quatre import fini_trois
    vn = var(n)
    succ_n = successeur(vn)
    e3n = exposant_cardinal_binaire(TROIS, vn)           # 3^n
    e3n1 = exposant_cardinal_binaire(TROIS, succ_n)      # 3^(n+1)
    prod = produit_cardinal_binaire(e3n, TROIS)          # 3^n·3

    from bourbaki.entiers.ensembles_fini_trois_quatre import trois_est_un_cardinal
    hstep = N.assume(et(est_fini(vn), _P_trois_impair(vn)))
    fini_n = conjonction_elim_gauche(hstep)              # Fini n
    Pn = conjonction_elim_droite(hstep)                  # impair(3^n)

    # 3^(n+1) = 3^n·3   (step 1 : est_cardinal 3 et Fini n)
    card_3 = trois_est_un_cardinal()                     # est_cardinal 3
    eqsucc = N.modus_ponens(conjonction_intro(card_3, fini_n),
                            _psi_base_t(TROIS, vn))   # 3^(n+1) = 3^n·3  (capture-safe base)

    # impair(3^n·3) via impair_fois_impair(3^n, 3) : Fini 3^n, Fini 3, impair 3^n, impair 3
    fini_3n = N.modus_ponens(fini_n, trois_puissance_dans_NN(vn))   # Fini(3^n)
    f3 = fini_trois()                                    # Fini 3
    imp3 = trois_impair()                                # impair 3
    ifi = instancie(instancie(N.generalisation("aifi3", N.generalisation("bifi3",
            impair_fois_impair("aifi3", "bifi3"))), e3n), TROIS)
    impair_prod = N.modus_ponens(conjonction_intro(conjonction_intro(fini_3n, f3),
                                                   conjonction_intro(Pn, imp3)), ifi)  # impair(3^n·3)
    # transport 3^n·3 → 3^(n+1)  (3^(n+1) = 3^n·3 ⇒ 3^n·3 = 3^(n+1))
    prod_eq_succ = N.modus_ponens(eqsucc, symetrie(e3n1, prod))   # 3^n·3 = 3^(n+1)
    leib = N.modus_ponens(prod_eq_succ,
        N.s6(prod, e3n1, "wtps", est_impair_propre(var("wtps"))))
    Pn1 = N.modus_ponens(impair_prod, equivalence_avant(leib))   # impair(3^(n+1))
    assert Pn1.conclusion == _P_trois_impair(succ_n), "step trois_impair : P[n+1] mal formé"
    body = N.loi_deduction(et(est_fini(vn), _P_trois_impair(vn)), Pn1)
    return N.generalisation(n, body)


def trois_puiss_impair(n="ntpi", k="ktpi"):
    """🎯 ⊢ Fini n ⇒ est_impair_propre(3^n).   (3^n est IMPAIR.)

    Récurrence C61 sur n : base 3^0=1 impair (un_impair) ; pas 3^(n+1)=3^n·3
    (step1) impair·impair impair (3 impair, impair_fois_impair)."""
    from bourbaki.entiers.ensembles_recurrence_C61 import _fini_et_P_implique_succ
    from bourbaki.entiers.ensembles_principe_recurrence_preuve import (
        principe_recurrence_preuve, predecesseur_fini_universel,
    )
    from bourbaki.entiers.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    vn = _t(n)
    P = _P_trois_impair
    p0 = _trois_puiss_impair_P0()
    step = _trois_puiss_impair_step("ntpis")
    assert p0.conclusion == P(ZERO), "P[0] mal formé"
    assert step.conclusion == _fini_et_P_implique_succ(P, "ntpis"), "pas mal formé"

    princ_imp = principe_recurrence_preuve(P, "ntpis", k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "pfu absent"
    princ_imp = _cut(princ_imp, pfu, predecesseur_fini_universel_preuve(k=k))
    fini_implique_Pn = N.modus_ponens(conjonction_intro(p0, step), princ_imp)  # (∀n)(Fini n⇒P[n])

    h = N.assume(est_fini(vn))
    Pn = N.modus_ponens(h, instancie(fini_implique_Pn, vn))
    res = N.loi_deduction(est_fini(vn), Pn)
    assert res.conclusion == trois_puiss_impair_cible(n), \
        f"trois_puiss_impair : conclusion inattendue\n{res.conclusion}"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (3)  2^k EST PAIR pour k≥1  —  (Fini k et k≠0) ⇒ est_pair_propre(2^k)
# ══════════════════════════════════════════════════════════════════════════════
def deux_puiss_pair_cible(k="kdpp"):
    from bourbaki.cardinaux.ensembles_divisibilite_propre import est_pair_propre
    vk = _t(k)
    return impl(et(est_fini(vk), non(egal(vk, ZERO))),
                est_pair_propre(exposant_cardinal_binaire(DEUX, vk)))


def deux_puiss_pair(k="kdpp"):
    """🎯 ⊢ (Fini k et k≠0) ⇒ est_pair_propre(2^k).   (2^k PAIR pour k≥1.)

    k≠0 ⇒ k=succ(k') prédécesseur (predecesseur_fini_universel_preuve), k' fini ;
    2^k = 2^(k'+1) = 2^k'·2 (step1) = 2·2^k' (commut) ; témoin q=2^k' (Fini, 2^k'∈ℕ)
    ⇒ divise_propre(2, 2^k)."""
    from bourbaki.cardinaux.ensembles_divisibilite_propre import est_pair_propre
    from bourbaki.cardinaux.ensembles_parite_iii5 import _comm_prod_t
    from bourbaki.cardinaux.ensembles_puissance_deux_trois_NN import deux_puissance_dans_NN
    from bourbaki.entiers.ensembles_fini_deux import deux_est_un_cardinal
    from bourbaki.entiers.ensembles_principe_recurrence_preuve import predecesseur_fini
    from bourbaki.entiers.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    from bourbaki.cardinaux.ensembles_cardinaux import inf_strict_card
    from bourbaki.entiers.ensembles_fini_successeur import fini_successeur_implique_fini
    vk = _t(k)
    e2k = exposant_cardinal_binaire(DEUX, vk)            # 2^k
    h = N.assume(et(est_fini(vk), non(egal(vk, ZERO))))
    fini_k = conjonction_elim_gauche(h)
    k_ne0 = conjonction_elim_droite(h)
    card_k = conjonction_elim_gauche(fini_k)

    # k = succ(k') prédécesseur (∃kp)((k=succ kp et card kp) et kp<k)
    pred = N.modus_ponens(conjonction_intro(fini_k, k_ne0),
                          instancie(predecesseur_fini_universel_preuve(), vk))
    vkp = var("kpred")
    corps = et(et(egal(vk, successeur(vkp)), est_cardinal(vkp)), inf_strict_card(vkp, vk))
    hK = N.assume(corps)
    k_eq_succ = conjonction_elim_gauche(conjonction_elim_gauche(hK))   # k = succ kp
    card_kp = conjonction_elim_droite(conjonction_elim_gauche(hK))     # card kp
    # Fini kp : k=succ kp ⇒ Fini(succ kp) ; card kp ⇒ Fini(succ kp)⇒Fini kp
    eqv_fini = N.modus_ponens(k_eq_succ,
        N.s6(vk, successeur(vkp), "wfkp", est_fini(var("wfkp"))))  # Fini k ⇔ Fini(succ kp)
    fini_succkp = N.modus_ponens(fini_k, equivalence_avant(eqv_fini))  # Fini(succ kp)
    fsif = instancie(N.generalisation("afsk2", fini_successeur_implique_fini("afsk2")), vkp)
    fini_kp = N.modus_ponens(fini_succkp, N.modus_ponens(card_kp, fsif))   # Fini kp

    # 2^(kp+1) = 2^kp·2  (step1 : card 2 et Fini kp)
    e2kp = exposant_cardinal_binaire(DEUX, vkp)          # 2^kp
    eqsucc = N.modus_ponens(conjonction_intro(deux_est_un_cardinal(), fini_kp),
                            _psi_base_t(DEUX, vkp))   # 2^(kp+1) = 2^kp·2  (capture-safe base)
    # 2^k = 2^(kp+1)  (k=succ kp ⇒ Leibniz sur 2^•)
    e2k_eq_e2succkp = N.modus_ponens(k_eq_succ,
        congruence_terme(vk, successeur(vkp), exposant_cardinal_binaire(DEUX, var("wek")), w="wek"))  # 2^k=2^(kp+1)
    e2k_eq_prod = composer_egalites(e2k_eq_e2succkp, eqsucc)   # 2^k = 2^kp·2
    # 2^kp·2 = 2·2^kp  (commut)
    comm = _comm_prod_t(e2kp, DEUX)                      # Card(2^kp×2)=Card(2×2^kp) = 2^kp·2 = 2·2^kp
    two_e2kp = produit_cardinal_binaire(DEUX, e2kp)      # 2·2^kp
    e2k_eq_2e2kp = composer_egalites(e2k_eq_prod, comm)  # 2^k = 2·2^kp
    # témoin q = 2^kp : Fini(2^kp) et 2^k = 2·2^kp  ⇒ divise_propre(2, 2^k)
    fini_e2kp = N.modus_ponens(fini_kp, deux_puissance_dans_NN(vkp))   # Fini(2^kp)
    conj = conjonction_intro(fini_e2kp, e2k_eq_2e2kp)
    matrice = et(est_fini(var("qdiv")), egal(e2k, produit_cardinal_binaire(DEUX, var("qdiv"))))
    pair_2k = N.modus_ponens(conj, N.s5(matrice, e2kp, "qdiv"))   # est_pair_propre(2^k)
    assert pair_2k.conclusion == est_pair_propre(e2k), "pair 2^k mal formé"
    # éliminer le témoin kp
    imp_corps = N.loi_deduction(corps, pair_2k)
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
    ex_imp = existe_elimination(imp_corps, "kpred")
    out_body = N.modus_ponens(pred, ex_imp)
    res = N.loi_deduction(et(est_fini(vk), non(egal(vk, ZERO))), out_body)
    assert res.conclusion == deux_puiss_pair_cible(k), \
        f"deux_puiss_pair : conclusion inattendue\n{res.conclusion}"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  SIMPLIFICATION MULTIPLICATIVE FINIE  —  (c≠0 et a·c=b·c) ⇒ a=b
#    Via TRICHOTOMIE (CLOS) + produit_strict_monotone (CLOS) :
#    a<b ⇒ a·c<b·c ⇒ a·c≠b·c (contra) ; b<a ⇒ symétrique ; reste a=b.
# ══════════════════════════════════════════════════════════════════════════════
def simplification_multiplicative_cible(a="asm", b="bsm", c="csm"):
    va, vb, vc = _t(a), _t(b), _t(c)
    ac = produit_cardinal_binaire(va, vc)
    bc = produit_cardinal_binaire(vb, vc)
    return impl(et(et(est_entier(va), et(est_entier(vb), est_entier(vc))),
                   et(non(egal(vc, ZERO)), egal(ac, bc))),
                egal(va, vb))


def simplification_multiplicative(a="asm", b="bsm", c="csm", d="dsm"):
    """🎯 ⊢ (entier a, entier b, entier c, c≠0, a·c=b·c) ⇒ a=b.   (CANCELLATION ℕ.)

    Trichotomie (a<b ou a=b ou b<a) ; produit_strict_monotone : a<b⇒a·c<b·c (⇒ a·c≠b·c),
    contredit a·c=b·c ; b<a symétrique ; donc a=b."""
    from bourbaki.entiers.ensembles_finis_props import trichotomie_finis
    from bourbaki.entiers.ensembles_prop3_strict_mono_iii5 import produit_strict_monotone
    from bourbaki.cardinaux.ensembles_cardinaux import inf_strict_card
    from bourbaki.logique.tactiques.tactiques_abrege2 import cas
    va, vb, vc = _t(a), _t(b), _t(c)
    ac = produit_cardinal_binaire(va, vc)
    bc = produit_cardinal_binaire(vb, vc)

    ante = et(et(est_entier(va), et(est_entier(vb), est_entier(vc))),
              et(non(egal(vc, ZERO)), egal(ac, bc)))
    h = N.assume(ante)
    hent = conjonction_elim_gauche(h)
    ent_a = conjonction_elim_gauche(hent)
    ent_b = conjonction_elim_gauche(conjonction_elim_droite(hent))
    ent_c = conjonction_elim_droite(conjonction_elim_droite(hent))
    hrest = conjonction_elim_droite(h)
    c_ne0 = conjonction_elim_gauche(hrest)
    acbc_eq = conjonction_elim_droite(hrest)            # a·c = b·c

    # produit_strict_monotone capture-safe (NOMS frais) : (ent a et ent b et ent c et c≠0 et a<b)⇒a·c<b·c
    def _psm_t(x, y):
        g = produit_strict_monotone("aPM", "bPM", "cPM", d)
        gen = N.generalisation("aPM", N.generalisation("bPM", N.generalisation("cPM", g)))
        return instancie(instancie(instancie(gen, _t(x)), _t(y)), vc)

    tri = trichotomie_finis(va, vb)                    # a<b ou (a=b ou b<a)

    # branche a<b : a·c<b·c ⇒ a·c≠b·c, contredit a·c=b·c
    h_lt_ab = N.assume(inf_strict_card(va, vb))
    psm_ab = _psm_t(va, vb)
    lt_acbc = N.modus_ponens(conjonction_intro(ent_a, conjonction_intro(ent_b,
                  conjonction_intro(ent_c, conjonction_intro(c_ne0, h_lt_ab)))), psm_ab)  # a·c<b·c
    ne_acbc = conjonction_elim_droite(lt_acbc)         # ¬(a·c=b·c)
    falso_ab = N.modus_ponens(acbc_eq, N.modus_ponens(ne_acbc, N.s2(non(egal(ac, bc)), egal(va, vb))))
    branch_ab = N.loi_deduction(inf_strict_card(va, vb), falso_ab)   # (a<b)⇒(a=b)

    # branche b<a : symétrique ⇒ b·c<a·c ⇒ ¬(b·c=a·c) ; a·c=b·c ⇒ b·c=a·c (sym), contra
    h_lt_ba = N.assume(inf_strict_card(vb, va))
    psm_ba = _psm_t(vb, va)
    lt_bcac = N.modus_ponens(conjonction_intro(ent_b, conjonction_intro(ent_a,
                  conjonction_intro(ent_c, conjonction_intro(c_ne0, h_lt_ba)))), psm_ba)  # b·c<a·c
    ne_bcac = conjonction_elim_droite(lt_bcac)         # ¬(b·c=a·c)
    bcac_eq = N.modus_ponens(acbc_eq, symetrie(ac, bc))   # b·c=a·c
    falso_ba = N.modus_ponens(bcac_eq, N.modus_ponens(ne_bcac, N.s2(non(egal(bc, ac)), egal(va, vb))))
    branch_ba = N.loi_deduction(inf_strict_card(vb, va), falso_ba)   # (b<a)⇒(a=b)

    # branche a=b : trivial
    branch_eq = N.loi_deduction(egal(va, vb), N.assume(egal(va, vb)))   # (a=b)⇒(a=b)

    # cas : a<b ou (a=b ou b<a)
    sub_disj = ou(egal(va, vb), inf_strict_card(vb, va))
    h_sub = N.assume(sub_disj)
    inner_cas = cas(h_sub, branch_eq, branch_ba)       # a=b  [sous (a=b ou b<a)]
    inner_imp = N.loi_deduction(sub_disj, inner_cas)   # (a=b ou b<a) ⇒ (a=b)
    a_eq_b = cas(tri, branch_ab, inner_imp)            # a=b
    res = N.loi_deduction(ante, a_eq_b)
    assert res.conclusion == simplification_multiplicative_cible(a, b, c), \
        f"simplification_multiplicative : conclusion inattendue\n{res.conclusion}"
    return res


__all__ = [
    "puissance_succ_eq_incond", "puissance_succ_eq_incond_cible",
    "trois_impair",
    "trois_puiss_impair", "trois_puiss_impair_cible",
    "deux_puiss_pair", "deux_puiss_pair_cible",
    "simplification_multiplicative", "simplification_multiplicative_cible",
]
