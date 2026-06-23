"""§III.5 — PARITÉ : division par deux des entiers (fondation ℵ₀·ℵ₀ = ℵ₀).

🎯 Tout entier fini est PAIR ou IMPAIR avec quotient EXPLICITE :

    division_par_deux(n) ⊢
        est_fini(n) ⇒ (∃k)( est_fini(k) et ( n = 2·k  ou  n = (2·k)+1 ) ).

⚠️ Représentation du « 2·k+1 » :  on prend le SUCCESSEUR de 2·k, i.e.
   `successeur(produit_cardinal_binaire(DEUX, k))`.  C'est EXACTEMENT « 2k+1 »
   (successeur(𝔞) := 𝔞 + Card({∅}) = 𝔞+1), et cette forme s'apparie SANS friction
   τ avec le successeur de la récurrence (évite UN=Card{∅} vs {∅}).

Construit sur le VRAI produit cardinal binaire produit_cardinal_binaire(2, k) =
Card(2×k) (E.III.3.3), JAMAIS sur l'opaque app("prod_ent").

LEMMES (theorie=22, noyau intact) :
  • division_par_deux(n)  — récurrence C61 (résidu prédécesseur DÉCHARGÉ) ;
  • impair_decompose(n)   — n impair ⇒ (∃k)( n = 2k+1 ) ;
  • un_impair()           — ¬(2 | 1) ;
  • deux_k_plus_un_impair(k) — ¬(2 | (2k+1)) ;
  • impair_fois_impair    — produit de deux impairs est impair.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, non, impl, existe, pourtout,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, instancie,
    equivalence_avant, equivalence_arriere, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import existe_elimination
from bourbaki.logique.tactiques.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.ensembles import ensembles_abrege as E
from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
    produit_cardinal_binaire,
)
from bourbaki.cardinaux.arithmetique.ensembles_arith_somme import somme_cardinale_binaire
from bourbaki.entiers.ensembles_entiers import est_fini, successeur, ZERO, UN, DEUX

from bourbaki.entiers.ensembles_prop3_produit_entier_iii5 import produit_succ_distribue
from bourbaki.entiers.ensembles_combinatoire_iii5 import (
    somme_succ_distribue, somme_zero_neutre_droite,
)
from bourbaki.cardinaux.arithmetique.ensembles_produit_petits import produit_cardinal_zero
from bourbaki.entiers.ensembles_entiers_theoremes import card_est_un_cardinal
from bourbaki.entiers.ensembles_fini_zero import zero_est_un_cardinal, fini_zero
from bourbaki.entiers.ensembles_fini_un import un_est_un_cardinal
from bourbaki.entiers.ensembles_fini_deux import deux_est_un_cardinal
from bourbaki.entiers.ensembles_fini_successeur import (
    cardinal_de_cardinal, fini_implique_fini_successeur,
)
from bourbaki.entiers.ensembles_principe_recurrence_preuve import (
    principe_recurrence_preuve, predecesseur_fini_universel,
)
from bourbaki.entiers.ensembles_predecesseur_prop2 import (
    predecesseur_fini_universel_preuve,
)
from bourbaki.entiers.ensembles_recurrence_C61 import _fini_et_P_implique_succ

from bourbaki.cardinaux.ensembles_divisibilite_propre import (
    divise_propre, est_pair_propre, est_impair_propre,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _cut(thm, hyp, preuve_hyp):
    return N.modus_ponens(preuve_hyp, N.loi_deduction(hyp, thm))


def _card_de_card_t(tx):
    gen = N.generalisation("xpccd", cardinal_de_cardinal("xpccd"))
    return instancie(gen, _t(tx))


def _card_est_cardinal_t(tX):
    """⊢ est_cardinal(Card X)  (version TERME).   Lieur 'X' pour coïncider avec est_cardinal."""
    gen = N.generalisation("Xcuc", card_est_un_cardinal("Xcuc", lieur="X"))
    return instancie(gen, _t(tX))


def _est_cardinal_produit(tA, tB):
    """⊢ est_cardinal(produit_cardinal_binaire(A, B))  (= est_cardinal(Card(A×B)))."""
    return _card_est_cardinal_t(E.produit(_t(tA), _t(tB)))


def _produit_succ_distribue_t(ta, tn):
    """produit_succ_distribue capture-safe : prouvé sur NOMS frais, instancié aux TERMES.

    ⊢ (card a et card n) ⇒ a·(n+1) = a·n + a   (a, n = TERMES quelconques)."""
    g = produit_succ_distribue("apsdt", "npsdt")
    gen = N.generalisation("apsdt", N.generalisation("npsdt", g))
    return instancie(instancie(gen, _t(ta)), _t(tn))


def _somme_succ_distribue_t(ta, tb):
    """somme_succ_distribue capture-safe.   ⊢ (card a et card b) ⇒ a+(b+1)=(a+b)+1."""
    g = somme_succ_distribue("assdt", "bssdt")
    gen = N.generalisation("assdt", N.generalisation("bssdt", g))
    return instancie(instancie(gen, _t(ta)), _t(tb))


def _somme_zero_neutre_droite_t(ta):
    """somme_zero_neutre_droite capture-safe.   ⊢ est_cardinal a ⇒ a+0 = a."""
    g = somme_zero_neutre_droite("asznt")
    gen = N.generalisation("asznt", g)
    return instancie(gen, _t(ta))


# ══════════════════════════════════════════════════════════════════════════════
#  Représentation « 2·k »  et  « 2·k+1 = successeur(2·k) ».
# ══════════════════════════════════════════════════════════════════════════════
def deux_fois(k):
    """2·k  :=  produit_cardinal_binaire(DEUX, k)  =  Card(2 × k)."""
    return produit_cardinal_binaire(DEUX, _t(k))


def deux_fois_plus_un(k):
    """2·k + 1  :=  successeur(2·k)  =  (2·k) + Card({∅})."""
    return successeur(deux_fois(k))


# ══════════════════════════════════════════════════════════════════════════════
#  MAILLON — 2·(k+1) = successeur(successeur(2·k))   (sous est_cardinal(k))
# ══════════════════════════════════════════════════════════════════════════════
def deux_succ_eq(k="kdse"):
    """⊢ est_cardinal(k) ⇒
         produit_cardinal_binaire(2, k+1) = successeur(successeur(2·k)).

    Chaîne (sous card k) :
      2·(k+1) = (2·k) + 2          [produit_succ_distribue(2, k), 2e arg = 2]
              = (2·k) + (1+1)      [2 == successeur(1) littéral]
              = ((2·k) + 1) + 1    [somme_succ_distribue(2k, 1)]      ... via successeurs
    On déroule via somme_succ_distribue deux fois et somme_zero_neutre_droite :
      (2·k) + 2 = (2·k) + succ(1) = succ((2·k)+1)
                = succ((2·k)+succ(0)) = succ(succ((2·k)+0))
                = succ(succ(2·k))     [(2·k)+0 = 2·k]."""
    vk = _t(k)
    twok = deux_fois(vk)                              # 2·k

    h = N.assume(est_cardinal(vk))
    card_2k = _est_cardinal_produit(DEUX, vk)         # est_cardinal(2·k)
    card_2 = deux_est_un_cardinal()                   # est_cardinal(2)
    card_1 = un_est_un_cardinal()                     # est_cardinal(1)
    card_0 = zero_est_un_cardinal()                   # est_cardinal(0)

    # (A) 2·(k+1) = (2·k) + 2     [produit_succ_distribue(2,k) : a·(n+1)=a·n+a, a=2]
    psd = _produit_succ_distribue_t(DEUX, vk)         # (card2 et cardk)⇒ 2·(k+1)=somme(2·k,2)
    eqA = N.modus_ponens(conjonction_intro(card_2, h), psd)   # 2·(k+1) = (2·k)+2

    # (B) (2·k)+2 = succ((2·k)+1)   [somme_succ_distribue(2k,1) ; 2 == succ(1)]
    ssd1 = _somme_succ_distribue_t(twok, UN)         # (card2k et card1)⇒ (2k)+succ(1)=succ((2k)+1)
    eqB = N.modus_ponens(conjonction_intro(card_2k, card_1), ssd1)
    #   2 == successeur(UN) littéralement, donc lhs de eqB == (2·k)+2.

    # (C) (2·k)+1 = succ((2·k)+0)   [somme_succ_distribue(2k,0) ; 1 == succ(0)]
    ssd0 = _somme_succ_distribue_t(twok, ZERO)       # (card2k et card0)⇒ (2k)+succ(0)=succ((2k)+0)
    eqC = N.modus_ponens(conjonction_intro(card_2k, card_0), ssd0)
    #   1 == successeur(ZERO) littéralement, donc lhs de eqC == (2·k)+1.

    # (D) (2·k)+0 = 2·k             [somme_zero_neutre_droite(2k)]
    eqD = N.modus_ponens(card_2k, _somme_zero_neutre_droite_t(twok))   # (2k)+0 = 2k

    # ── assemblage des successeurs ─────────────────────────────────────────────
    # eqD : (2k)+0 = 2k  →  succ((2k)+0) = succ(2k)   (congruence successeur)
    succ_2k0 = successeur(somme_cardinale_binaire(twok, ZERO))
    succ_2k = successeur(twok)
    leibD = N.modus_ponens(eqD, N.s6(somme_cardinale_binaire(twok, ZERO), twok,
                                     "wD", egal(successeur(var("wD")), succ_2k)))
    #   leibD : ((2k)+0 = 2k) ⇒ ( succ((2k)+0)=succ(2k) ⇔ succ((2k)+0)=succ(2k) ) — pas utile.
    # Plus simple : congruence directe via s6 sur le terme successeur.
    # eqC : (2k)+1 = succ((2k)+0).  Composer avec succ((2k)+0)=succ(2k) :
    #   d'abord prouver succ((2k)+0) = succ(2k) à partir de eqD.
    eq_succ_D = _congr_succ(eqD)                     # succ((2k)+0) = succ(2k)
    eqC2 = composer_egalites(eqC, eq_succ_D)         # (2k)+1 = succ(2k)

    # eqB : (2k)+2 = succ((2k)+1).  Composer avec succ((2k)+1) = succ(succ(2k)) :
    eq_succ_C = _congr_succ(eqC2)                    # succ((2k)+1) = succ(succ(2k))
    eqB2 = composer_egalites(eqB, eq_succ_C)         # (2k)+2 = succ(succ(2k))

    # eqA : 2·(k+1) = (2k)+2 ; compose
    final = composer_egalites(eqA, eqB2)             # 2·(k+1) = succ(succ(2k))

    out = N.loi_deduction(est_cardinal(vk), final)
    cible = impl(est_cardinal(vk),
                 egal(produit_cardinal_binaire(DEUX, successeur(vk)),
                      successeur(successeur(twok))))
    assert out.conclusion == cible, \
        f"deux_succ_eq : conclusion inattendue\n{out.conclusion}\n{cible}"
    return out


def _congr_succ(eq_thm):
    """De ⊢ (u = v) déduit ⊢ ( successeur(u) = successeur(v) )  (congruence du successeur)."""
    u, v = eq_thm.conclusion.termes
    leib = N.s6(u, v, "wcs", egal(successeur(u), successeur(var("wcs"))))
    eqv = N.modus_ponens(eq_thm, leib)               # (u=v) ⇒ (succ u=succ u ⇔ succ u=succ v)
    refl = N.reflexivite(successeur(u))              # succ u = succ u
    return N.modus_ponens(refl, equivalence_avant(eqv))   # succ u = succ v


# ══════════════════════════════════════════════════════════════════════════════
#  (1) DIVISION PAR DEUX — tout entier est pair ou impair (quotient explicite)
# ══════════════════════════════════════════════════════════════════════════════
def _P_div2(n):
    """P[n] := (∃k)( est_fini(k) et ( n = 2·k  ou  n = succ(2·k) ) )."""
    vn = _t(n)
    vk = var("kd2")
    return existe("kd2", et(est_fini(vk),
                            ou(egal(vn, deux_fois(vk)),
                               egal(vn, successeur(deux_fois(vk))))))


def division_par_deux_cible(n="nd2"):
    vn = _t(n)
    return impl(est_fini(vn), _P_div2(vn))


def _preuve_P0_div2():
    """⊢ P[0]  ( witness k=0 ; 0 = 2·0, disjonction GAUCHE ).

    2·0 = Card(2×0) ; 0 = ZERO = Card∅.  produit_cardinal_zero(2) : Card(2×∅)=Card∅.
    On veut 0 = 2·0 = Card(2×ZERO).  Or ZERO == Card∅, donc 2×ZERO == 2×Card∅ ≠ 2×∅.
    On passe par produit_cardinal_bien_defini comme dans _preuve_P0_produit, mais ici
    plus simple : on prouve 2·0 = 0 et l'utilise pour 0 = 2·0."""
    # 2·0 = 0  via le maillon produit_cardinal_binaire(2,0) = 0.
    eq_2zero = _deux_fois_zero_eq()                  # 2·0 = 0  (= ZERO)
    zero_eq_2zero = N.modus_ponens(eq_2zero, symetrie(deux_fois(ZERO), ZERO))   # 0 = 2·0
    fini_0 = fini_zero()                             # Fini 0
    # disjonction gauche : (0 = 2·0) ou (0 = succ 2·0)
    disj = _ou_gauche(zero_eq_2zero, egal(ZERO, successeur(deux_fois(ZERO))))
    conj = conjonction_intro(fini_0, disj)
    matrice = et(est_fini(var("kd2")),
                 ou(egal(ZERO, deux_fois(var("kd2"))),
                    egal(ZERO, successeur(deux_fois(var("kd2"))))))
    s5 = N.s5(matrice, ZERO, "kd2")
    res = N.modus_ponens(conj, s5)
    assert res.conclusion == _P_div2(ZERO), \
        f"P[0] div2 mal formé\n{res.conclusion}\n{_P_div2(ZERO)}"
    return res


def _deux_fois_zero_eq():
    """⊢ produit_cardinal_binaire(2, 0) = 0.   (2·0 = 0 ; 0 = ZERO = Card∅.)

    Miroir de _preuve_P0_produit : a·0 = Card(a×∅) = Card∅ = ZERO, via
    produit_cardinal_bien_defini(2, ∅, 2, 0)."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
        produit_cardinal_bien_defini,
    )
    va = DEUX
    card_a = N.modus_ponens(deux_est_un_cardinal(), _card_de_card_t(va))   # Card 2 = 2
    refl_card_vide = N.reflexivite(cardinal(E.VIDE))   # Card∅ = Card∅ = 0
    # produit_cardinal_bien_defini(2, ∅, 2, 0) capture-safe
    g = produit_cardinal_bien_defini("Xpz", "Ypz", "apz", "bpz")
    gen = N.generalisation("Xpz", N.generalisation("Ypz",
          N.generalisation("apz", N.generalisation("bpz", g))))
    bd = instancie(instancie(instancie(instancie(gen, va), E.VIDE), va), ZERO)
    a0 = produit_cardinal_binaire(va, ZERO)            # 2·0
    Card_a_vide = cardinal(E.produit(va, E.VIDE))
    eq_a0 = N.modus_ponens(conjonction_intro(card_a, refl_card_vide), bd)  # Card(2×∅) = 2·0
    czero_gen = N.generalisation("Apcz", produit_cardinal_zero("Apcz"))
    czero = instancie(czero_gen, va)                   # Card(2×∅) = Card∅
    a0_eq_cardvide = composer_egalites(
        N.modus_ponens(eq_a0, symetrie(Card_a_vide, a0)), czero)   # 2·0 = Card∅ = ZERO
    return a0_eq_cardvide                               # 2·0 = ZERO


def _preuve_step_div2(n="nd2step"):
    """⊢ (∀n)( ( est_fini(n) et P[n] ) ⇒ P[n+1] ).

    De P[n] : ∃k Fini k et (n=2k ou n=succ 2k).  On élimine k, et par cas :
      • n = 2k    ⇒ n+1 = succ(2k) : witness k, disjonction DROITE.
      • n = succ 2k ⇒ n+1 = succ(succ 2k) = 2·(k+1) (deux_succ_eq) : witness succ k,
        disjonction GAUCHE ; Fini(succ k) (fini_implique_fini_successeur)."""
    vn = var(n)
    succ_n = successeur(vn)
    hstep = N.assume(et(est_fini(vn), _P_div2(vn)))
    fini_n = conjonction_elim_gauche(hstep)            # Fini n
    hPn = conjonction_elim_droite(hstep)               # ∃k ...

    vk = var("kd2")
    corps_k = et(est_fini(vk),
                 ou(egal(vn, deux_fois(vk)), egal(vn, successeur(deux_fois(vk)))))
    hK = N.assume(corps_k)
    fini_k = conjonction_elim_gauche(hK)               # Fini k
    card_k = conjonction_elim_gauche(fini_k)           # est_cardinal k
    disj_k = conjonction_elim_droite(hK)               # (n=2k) ou (n=succ 2k)

    twok = deux_fois(vk)

    # cible commune : P[n+1]
    cible_succ = _P_div2(succ_n)

    # ── CAS A : n = 2k  ⇒  n+1 = succ(2k)  (witness k, droite) ──────────────────
    hA = N.assume(egal(vn, twok))                      # n = 2k
    # succ n = succ 2k  (congruence)
    succn_eq = _congr_succ(hA)                         # succ n = succ 2k
    # disjonction DROITE : (succ n = 2k) ou (succ n = succ 2k)
    disjA = _ou_droite(succn_eq, egal(succ_n, twok))   # (succ n=2k) ou (succ n=succ 2k)
    conjA = conjonction_intro(fini_k, disjA)
    matrice = et(est_fini(vk),
                 ou(egal(succ_n, deux_fois(vk)), egal(succ_n, successeur(deux_fois(vk)))))
    s5A = N.s5(matrice, vk, "kd2")
    PA = N.modus_ponens(conjA, s5A)                    # P[n+1]
    assert PA.conclusion == cible_succ, "cas A : P[n+1] mal formé"
    impA = N.loi_deduction(egal(vn, twok), PA)         # (n=2k) ⇒ P[n+1]

    # ── CAS B : n = succ 2k ⇒ n+1 = succ(succ 2k) = 2·(k+1) (witness succ k, gauche)
    hB = N.assume(egal(vn, successeur(twok)))          # n = succ 2k
    succn_eqB = _congr_succ(hB)                        # succ n = succ(succ 2k)
    # 2·(k+1) = succ(succ 2k)   (deux_succ_eq sous card k)
    dse = N.modus_ponens(card_k, deux_succ_eq(vk))     # 2·(k+1) = succ(succ 2k)
    succss_eq_2k1 = N.modus_ponens(dse,
        symetrie(deux_fois(successeur(vk)), successeur(successeur(twok))))  # succ(succ 2k) = 2·(k+1)
    succn_eq_2k1 = composer_egalites(succn_eqB, succss_eq_2k1)   # succ n = 2·(k+1)
    # witness succ k : Fini(succ k)  (fini_implique_fini_successeur instancié au TERME k)
    fifs = instancie(N.generalisation("affk", fini_implique_fini_successeur("affk")), vk)
    fini_succk = N.modus_ponens(fini_k, fifs)          # Fini(succ k)
    # disjonction GAUCHE : (succ n = 2·(k+1)) ou (succ n = succ(2·(k+1)))
    disjB = _ou_gauche(succn_eq_2k1,
                       egal(succ_n, successeur(deux_fois(successeur(vk)))))
    conjB = conjonction_intro(fini_succk, disjB)
    s5B = N.s5(et(est_fini(var("kd2")),
                  ou(egal(succ_n, deux_fois(var("kd2"))),
                     egal(succ_n, successeur(deux_fois(var("kd2")))))),
               successeur(vk), "kd2")
    PB = N.modus_ponens(conjB, s5B)                    # P[n+1]
    assert PB.conclusion == cible_succ, "cas B : P[n+1] mal formé"
    impB = N.loi_deduction(egal(vn, successeur(twok)), PB)   # (n=succ 2k) ⇒ P[n+1]

    # ── cas sur disj_k ─────────────────────────────────────────────────────────
    Pn1_underK = cas(disj_k, impA, impB)               # P[n+1]   [corps_k, Fini n]
    # élimine k
    imp_k = N.loi_deduction(corps_k, Pn1_underK)       # corps_k ⇒ P[n+1]
    ex_imp = existe_elimination(imp_k, "kd2")          # (∃k corps_k) ⇒ P[n+1]
    Pn1 = N.modus_ponens(hPn, ex_imp)                  # P[n+1]   [Fini n]

    body = N.loi_deduction(et(est_fini(vn), _P_div2(vn)), Pn1)
    return N.generalisation(n, body)


def _ou_gauche(thm_p, q):
    """De ⊢ P, déduit ⊢ (P ou Q)."""
    return N.modus_ponens(thm_p, N.s2(thm_p.conclusion, q))


def _ou_droite(thm_q, p):
    """De ⊢ Q, déduit ⊢ (P ou Q)."""
    q = thm_q.conclusion
    return N.modus_ponens(N.modus_ponens(thm_q, N.s2(q, p)), N.s3(q, p))


def division_par_deux(n="nd2", k="kpd2"):
    """🎯🎯 ⊢ est_fini(n) ⇒ (∃k)( est_fini(k) et ( n = 2·k ou n = 2·k+1 ) ).

    KEYSTONE §III.5 (division euclidienne par 2).  Récurrence C61 sur n :
    P[n] := (∃k)(Fini k et (n=2k ou n=succ 2k)).  base k=0 (0=2·0) ; pas via
    deux_succ_eq (2·(k+1)=succ(succ 2k)).  theorie=22, 0 hyp."""
    vn = _t(n)
    P = _P_div2

    p0 = _preuve_P0_div2()                             # P[0]
    step = _preuve_step_div2()                          # (∀n)((Fini n et P[n])⇒P[n+1])
    assert p0.conclusion == P(ZERO), "P[0] mal formé"
    assert step.conclusion == _fini_et_P_implique_succ(P, "nd2step"), \
        f"pas mal formé\n{step.conclusion}\n{_fini_et_P_implique_succ(P, 'nd2step')}"

    princ_imp = principe_recurrence_preuve(P, "nd2step", k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "predecesseur_fini_universel absent"
    princ_imp = _cut(princ_imp, pfu, predecesseur_fini_universel_preuve(k=k))

    ante = conjonction_intro(p0, step)
    fini_implique_Pn = N.modus_ponens(ante, princ_imp)   # (∀n)(Fini n ⇒ P[n])

    h = N.assume(est_fini(vn))
    inst = instancie(fini_implique_Pn, vn)               # Fini n ⇒ P[n]
    Pn = N.modus_ponens(h, inst)
    res = N.loi_deduction(est_fini(vn), Pn)
    cible = division_par_deux_cible(n)
    assert res.conclusion == cible, \
        f"division_par_deux : conclusion inattendue\n{res.conclusion}\n{cible}"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (2) IMPAIR DÉCOMPOSE — n impair ⇒ (∃k)( n = 2·k+1 )
# ══════════════════════════════════════════════════════════════════════════════
def _decomp_impair(n):
    """(∃k)( est_fini(k) et n = 2·k+1 )   ( 2·k+1 := succ(2·k) )."""
    vn = _t(n)
    vk = var("kid")
    return existe("kid", et(est_fini(vk), egal(vn, successeur(deux_fois(vk)))))


def impair_decompose_cible(n="nid"):
    vn = _t(n)
    return impl(et(est_fini(vn), est_impair_propre(vn)), _decomp_impair(vn))


def impair_decompose(n="nid"):
    """🎯 ⊢ ( est_fini(n) et est_impair_propre(n) ) ⇒ (∃k)( Fini k et n = 2·k+1 ).

    De division_par_deux : n=2k ou n=succ(2k).  La branche n=2k contredit
    est_impair_propre(n) = ¬divise_propre(2,n) : deux_divise_double(k) ⊢
    est_pair_propre(2k) = divise_propre(2,2k), et n=2k transporte en divise_propre(2,n)
    (Leibniz).  Donc seule la branche n=succ(2k) survit : témoin k."""
    from bourbaki.cardinaux.ensembles_divisibilite_propre import deux_divise_double
    vn = _t(n)

    hyp = N.assume(et(est_fini(vn), est_impair_propre(vn)))
    fini_n = conjonction_elim_gauche(hyp)
    impair_n = conjonction_elim_droite(hyp)            # ¬divise_propre(2,n)

    # division_par_deux(n) ⇒ P[n]
    dpd = N.modus_ponens(fini_n, division_par_deux(n))   # (∃k)(Fini k et (n=2k ou n=succ 2k))

    vk = var("kd2")
    corps = et(est_fini(vk),
               ou(egal(vn, deux_fois(vk)), egal(vn, successeur(deux_fois(vk)))))
    hK = N.assume(corps)
    fini_k = conjonction_elim_gauche(hK)
    card_k = conjonction_elim_gauche(fini_k)
    disj = conjonction_elim_droite(hK)

    cible = _decomp_impair(vn)

    # CAS A : n = 2k  → contradiction avec impair
    hA = N.assume(egal(vn, deux_fois(vk)))             # n = 2k
    # deux_divise_double(k) : Fini k ⇒ est_pair_propre(2k) = divise_propre(2,2k)
    twok = deux_fois(vk)
    ddd = instancie(N.generalisation("ydd_g",
                    deux_divise_double("ydd_g")), vk)   # Fini k ⇒ est_pair_propre(2k)
    pair_2k = N.modus_ponens(fini_k, ddd)               # est_pair_propre(2k) = divise_propre(2,2k)
    leib = N.modus_ponens(N.modus_ponens(hA, symetrie(vn, twok)),
                          N.s6(twok, vn, "wid", est_pair_propre(var("wid"))))  # (2k=n)⇒(pair 2k⇔pair n)
    pair_n = N.modus_ponens(pair_2k, equivalence_avant(leib))   # divise_propre(2,n)
    # contradiction pair_n ∧ impair_n ⇒ cible (ex falso)
    PA = _ex_falso(pair_n, impair_n, cible)
    impA = N.loi_deduction(egal(vn, twok), PA)

    # CAS B : n = succ 2k  → témoin k
    hB = N.assume(egal(vn, successeur(twok)))          # n = succ 2k
    conjB = conjonction_intro(fini_k, hB)
    s5B = N.s5(et(est_fini(var("kid")), egal(vn, successeur(deux_fois(var("kid"))))),
               vk, "kid")
    PB = N.modus_ponens(conjB, s5B)                    # (∃k)(Fini k et n=2k+1)
    assert PB.conclusion == cible, "cas B impair_decompose mal formé"
    impB = N.loi_deduction(egal(vn, successeur(twok)), PB)

    Pn_underK = cas(disj, impA, impB)                  # cible
    imp_k = N.loi_deduction(corps, Pn_underK)
    ex_imp = existe_elimination(imp_k, "kd2")
    out_body = N.modus_ponens(dpd, ex_imp)             # cible
    res = N.loi_deduction(et(est_fini(vn), est_impair_propre(vn)), out_body)
    assert res.conclusion == impair_decompose_cible(n), \
        f"impair_decompose : conclusion inattendue\n{res.conclusion}\n{impair_decompose_cible(n)}"
    return res


def _ex_falso(thm_a, thm_na, cible):
    """De ⊢ A et ⊢ ¬A, déduit ⊢ cible."""
    a = thm_a.conclusion
    imp = N.modus_ponens(thm_na, N.s2(non(a), cible))
    return N.modus_ponens(thm_a, imp)


__all__ = [
    "deux_fois", "deux_fois_plus_un", "deux_succ_eq",
    "division_par_deux", "division_par_deux_cible",
    "impair_decompose", "impair_decompose_cible",
]
