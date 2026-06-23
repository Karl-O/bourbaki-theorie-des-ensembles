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
    symetrie, composer_egalites, congruence_terme,
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


def _refute_self(thm_P_imp_notP):
    """De ⊢ (P ⇒ ¬P) déduit ⊢ ¬P."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import antecedent_consequent
    P, notP = antecedent_consequent(thm_P_imp_notP.conclusion)
    return N.modus_ponens(thm_P_imp_notP, N.s1(notP))


# ══════════════════════════════════════════════════════════════════════════════
#  (3a) PARITÉ DISJOINTE — 2·a ≠ 2·b+1   (« pair ≠ impair »), par récurrence sur a.
# ══════════════════════════════════════════════════════════════════════════════
def _deux_succ_eq_t(tk):
    """deux_succ_eq capture-safe : ⊢ card k ⇒ 2·(k+1) = succ(succ(2·k))."""
    g = N.generalisation("kdset", deux_succ_eq("kdset"))
    return instancie(g, _t(tk))


def _prop8_t(tA, tB):
    """prop8_successeur_injectif capture-safe : ⊢ (succ A=succ B) ⇒ (Card A=Card B)."""
    from bourbaki.cardinaux.arithmetique.ensembles_prop8_fini2 import prop8_successeur_injectif
    g = N.generalisation("A", N.generalisation("B",
            prop8_successeur_injectif("A", "B")))
    return instancie(instancie(g, _t(tA)), _t(tB))


def _succ_inj_cardinaux(eq_succ, tA, tB):
    """De ⊢ (succ A = succ B), A et B cardinaux (preuves cA, cB), déduit ⊢ A = B.

    prop8 ⇒ Card A=Card B ; cardinal_de_cardinal sur A et B ⇒ A=B."""
    vA, vB = _t(tA), _t(tB)
    cardA_eq_cardB = N.modus_ponens(eq_succ, _prop8_t(vA, vB))   # Card A = Card B
    return cardA_eq_cardB   # caller composes with Card=id


def _succ_non_nul_t(tk):
    """⊢ ¬(successeur(k) = 0)  (version TERME)."""
    from bourbaki.entiers.ensembles_aleph0 import successeur_non_nul
    g = N.generalisation("jsnn", successeur_non_nul("jsnn"))
    return instancie(g, _t(tk))


def _Qpni(a):
    """Q[a] := (∀b)( Fini b ⇒ ¬( 2·a = 2·b+1 ) )   ( 2·b+1 := succ(2·b) )."""
    va = _t(a)
    vb = var("bpni")
    return pourtout("bpni", impl(est_fini(vb),
                non(egal(deux_fois(va), successeur(deux_fois(vb))))))


def _pni_P0():
    """⊢ Q[0]   : (∀b)( Fini b ⇒ ¬(2·0 = succ(2·b)) ).

    2·0 = 0 ; succ(2·b) ≠ 0 (successeur_non_nul) ⇒ 0 ≠ succ(2·b)."""
    vb = var("bpni")
    twob = deux_fois(vb)
    h = N.assume(est_fini(vb))
    # 2·0 = 0
    eq20 = _deux_fois_zero_eq()                        # 2·0 = ZERO
    # ¬(succ(2b) = 0)  ⇒ ¬(0 = succ 2b) ⇒ ¬(2·0 = succ 2b)
    snn = _succ_non_nul_t(twob)                        # ¬(succ 2b = 0)
    # ¬(succ 2b = 0) ⇒ ¬(0 = succ 2b)  (symétrie de l'égalité sous ¬)
    # build: assume 0 = succ 2b ; symétrie ⇒ succ 2b = 0 ; contradiction
    h0 = N.assume(egal(ZERO, successeur(twob)))        # 0 = succ 2b
    sb0 = N.modus_ponens(h0, symetrie(ZERO, successeur(twob)))   # succ 2b = 0
    contra = _ex_falso(sb0, snn, non(egal(ZERO, successeur(twob))))
    n0_ne = _refute_self(N.loi_deduction(egal(ZERO, successeur(twob)), contra))  # ¬(0=succ 2b)
    # transporte 2·0 = 0 :  ¬(0=succ 2b) ⇒ ¬(2·0 = succ 2b)  (Leibniz 0=2·0)
    zero_eq_20 = N.modus_ponens(eq20, symetrie(deux_fois(ZERO), ZERO))   # 0 = 2·0
    leib = N.modus_ponens(zero_eq_20,
        N.s6(ZERO, deux_fois(ZERO), "wpni0",
             non(egal(var("wpni0"), successeur(twob)))))   # (0=2·0)⇒(¬(0=succ2b)⇔¬(2·0=succ2b))
    res_ne = N.modus_ponens(n0_ne, equivalence_avant(leib))   # ¬(2·0 = succ 2b)
    body = N.loi_deduction(est_fini(vb), res_ne)
    out = N.generalisation("bpni", body)
    assert out.conclusion == _Qpni(ZERO), \
        f"Q[0] pni mal formé\n{out.conclusion}\n{_Qpni(ZERO)}"
    return out


def _pni_step(a="apni"):
    """⊢ (∀a)( (Fini a et Q[a]) ⇒ Q[a+1] ).   (cf. en-tête du module.)"""
    from bourbaki.entiers.ensembles_fini_successeur import (
        cardinal_de_cardinal, fini_successeur_implique_fini,
    )
    from bourbaki.entiers.ensembles_principe_recurrence_preuve import predecesseur_fini
    from bourbaki.entiers.ensembles_predecesseur_prop2 import (
        predecesseur_fini_universel_preuve,
    )
    va = var(a)
    hstep = N.assume(et(est_fini(va), _Qpni(va)))
    fini_a = conjonction_elim_gauche(hstep)
    Qa = conjonction_elim_droite(hstep)
    card_a = conjonction_elim_gauche(fini_a)           # est_cardinal a

    succ_a = successeur(va)
    twoa = deux_fois(va)                               # 2·a

    # Q[a+1] : fixe b, Fini b, assume 2·(a+1) = succ(2b), dérive ⊥.
    vb = var("bpni")
    twob = deux_fois(vb)
    hfb = N.assume(est_fini(vb))
    card_b = conjonction_elim_gauche(hfb)
    habs = N.assume(egal(deux_fois(succ_a), successeur(twob)))   # 2·(a+1) = succ 2b

    # 2·(a+1) = succ(succ 2a)   (deux_succ_eq, card a)
    dse = N.modus_ponens(card_a, _deux_succ_eq_t(va))  # 2·(a+1) = succ(succ 2a)
    succss2a_eq_succ2b = composer_egalites(
        N.modus_ponens(dse, symetrie(deux_fois(succ_a), successeur(successeur(twoa)))),
        habs)                                          # succ(succ 2a) = succ 2b
    # prop8 : Card(succ 2a) = Card(2b)  ⇒  succ 2a = 2b  (cardinaux)
    cc = _succ_inj_cardinaux(succss2a_eq_succ2b, successeur(twoa), twob)  # Card(succ 2a)=Card(2b)
    # Card(succ 2a) = succ 2a ; Card(2b) = 2b
    card_succ2a = _est_cardinal_succ(twoa)             # est_cardinal(succ 2a)
    card_2b = _est_cardinal_produit(DEUX, vb)          # est_cardinal(2b)
    eq_Cs2a = N.modus_ponens(card_succ2a, _card_de_card_t(successeur(twoa)))  # Card(succ2a)=succ2a
    eq_C2b = N.modus_ponens(card_2b, _card_de_card_t(twob))                   # Card(2b)=2b
    succ2a_eq_2b = composer_egalites(
        composer_egalites(N.modus_ponens(eq_Cs2a, symetrie(cardinal(successeur(twoa)), successeur(twoa))), cc),
        eq_C2b)                                        # succ 2a = 2b

    # ── sous-cas sur b : b=0 ou b=succ(b') ────────────────────────────────────
    cible = non(egal(deux_fois(succ_a), successeur(twob)))   # but Q[a+1] body : we derive ⊥→ce
    # On va dériver ⊥ (i.e. n'importe quoi) ; cible finale = ¬(2(a+1)=succ 2b).
    falso_target = non(egal(deux_fois(succ_a), successeur(twob)))

    # CAS b = 0 : 2b = 2·0 = 0, succ 2a ≠ 0.
    h_b0 = N.assume(egal(vb, ZERO))                    # b = 0
    # 2b = 2·0 (Leibniz b=0 sur deux_fois) puis 2·0=0
    eq_2b_2zero = _congr_deuxfois(h_b0)                # 2b = 2·0
    eq_2b_zero = composer_egalites(eq_2b_2zero, _deux_fois_zero_eq())   # 2b = 0
    # succ 2a = 2b = 0  ⇒  succ 2a = 0, contredit successeur_non_nul
    succ2a_eq_0 = composer_egalites(succ2a_eq_2b, eq_2b_zero)   # succ 2a = 0
    contra0 = _ex_falso(succ2a_eq_0, _succ_non_nul_t(twoa), falso_target)
    imp_b0 = N.loi_deduction(egal(vb, ZERO), contra0)  # (b=0) ⇒ falso_target

    # CAS b ≠ 0 : prédécesseur b = succ(b'), Fini b', 2b = succ(succ 2b'),
    #   ⇒ succ 2a = succ(succ 2b') ⇒ 2a = succ 2b', contredit Q[a] à b'.
    h_bne = N.assume(non(egal(vb, ZERO)))
    pred_b = N.modus_ponens(conjonction_intro(hfb, h_bne),
        instancie(predecesseur_fini_universel_preuve(), vb))   # (∃k)(b=succ k et card k et k<b)
    vk = var("kpred")
    corps_k = predecesseur_fini(vb).sous[0]            # body of ∃kpred
    # rebuild corps_k explicitly to assume it
    from bourbaki.cardinaux.ensembles_cardinaux import inf_strict_card
    corps_k = et(et(egal(vb, successeur(vk)), est_cardinal(vk)), inf_strict_card(vk, vb))
    hK = N.assume(corps_k)
    b_eq_succk = conjonction_elim_gauche(conjonction_elim_gauche(hK))   # b = succ k
    card_k = conjonction_elim_droite(conjonction_elim_gauche(hK))       # est_cardinal k
    # Fini k : b=succ k ⇒ Fini(succ k) ; card k ⇒ (Fini(succ k)⇒Fini k)
    fini_succk = N.modus_ponens(b_eq_succk,
        N.s6(vb, successeur(vk), "wfk", est_fini(var("wfk"))))   # Fini b ⇔ Fini(succ k)
    fini_succk2 = N.modus_ponens(hfb, equivalence_avant(fini_succk))   # Fini(succ k)
    fsif = instancie(N.generalisation("afsk", fini_successeur_implique_fini("afsk")), vk)
    fini_k = N.modus_ponens(fini_succk2, N.modus_ponens(card_k, fsif))   # Fini k
    # 2b = 2·(succ k) (Leibniz b=succ k) = succ(succ 2k) (deux_succ_eq, card k)
    eq_2b_2succk = _congr_deuxfois(b_eq_succk)         # 2b = 2·(succ k)
    dse_k = N.modus_ponens(card_k, _deux_succ_eq_t(vk))   # 2·(succ k) = succ(succ 2k)
    eq_2b_succss2k = composer_egalites(eq_2b_2succk, dse_k)   # 2b = succ(succ 2k)
    twok = deux_fois(vk)
    # succ 2a = 2b = succ(succ 2k)  ⇒ prop8 ⇒ Card(2a)=Card(succ 2k) ⇒ 2a = succ 2k
    succ2a_eq_succss2k = composer_egalites(succ2a_eq_2b, eq_2b_succss2k)   # succ 2a = succ(succ 2k)
    cc2 = _succ_inj_cardinaux(succ2a_eq_succss2k, twoa, successeur(twok))   # Card(2a)=Card(succ 2k)
    card_2a = _est_cardinal_produit(DEUX, va)
    card_succ2k = _est_cardinal_succ(twok)
    eq_C2a = N.modus_ponens(card_2a, _card_de_card_t(twoa))
    eq_Cs2k = N.modus_ponens(card_succ2k, _card_de_card_t(successeur(twok)))
    twoa_eq_succ2k = composer_egalites(
        composer_egalites(N.modus_ponens(eq_C2a, symetrie(cardinal(twoa), twoa)), cc2),
        eq_Cs2k)                                       # 2a = succ 2k
    # Q[a] à k : Fini k ⇒ ¬(2a = succ 2k)
    Qa_k = N.modus_ponens(fini_k, instancie(Qa, vk))   # ¬(2a = succ 2k)
    contraK = _ex_falso(twoa_eq_succ2k, Qa_k, falso_target)
    imp_corps_k = N.loi_deduction(corps_k, contraK)
    ex_imp = existe_elimination(imp_corps_k, "kpred")
    contra_bne = N.modus_ponens(pred_b, ex_imp)        # falso_target
    imp_bne = N.loi_deduction(non(egal(vb, ZERO)), contra_bne)

    # tiers exclu sur (b=0) : combine imp_b0 et imp_bne
    from bourbaki.logique.tactiques.tactiques_abrege2 import tiers_exclu
    te = tiers_exclu(egal(vb, ZERO))                   # (b=0) ou ¬(b=0)
    res_ne = cas(te, imp_b0, imp_bne)                  # falso_target = ¬(2(a+1)=succ 2b)

    # mais res_ne a été dérivé SOUS habs (2(a+1)=succ 2b). On a en fait une contradiction :
    # _ex_falso a produit falso_target = ¬(2(a+1)=succ 2b) sous habs. Donc habs ⇒ ¬habs ⇒ ¬habs.
    imp_self = N.loi_deduction(egal(deux_fois(succ_a), successeur(twob)), res_ne)
    final_ne = _refute_self(imp_self)                  # ¬(2(a+1) = succ 2b)
    body_b = N.loi_deduction(est_fini(vb), final_ne)
    Qa1 = N.generalisation("bpni", body_b)             # Q[a+1]
    assert Qa1.conclusion == _Qpni(succ_a), f"Q[a+1] pni mal formé"
    step_body = N.loi_deduction(et(est_fini(va), _Qpni(va)), Qa1)
    return N.generalisation(a, step_body)


def _congr_deuxfois(eq_thm):
    """De ⊢ (u = v) déduit ⊢ ( 2·u = 2·v )  (congruence de deux_fois)."""
    u, v = eq_thm.conclusion.termes
    leib = N.s6(u, v, "wcd", egal(deux_fois(u), deux_fois(var("wcd"))))
    eqv = N.modus_ponens(eq_thm, leib)
    refl = N.reflexivite(deux_fois(u))
    return N.modus_ponens(refl, equivalence_avant(eqv))


def _est_cardinal_succ(tk):
    """⊢ est_cardinal(successeur(k))   (successeur(k)=Card(k⊔{∅}))."""
    from bourbaki.ensembles.familles.ensembles_somme_disjointe import somme_disjointe
    return _card_est_cardinal_t(somme_disjointe(_t(tk), E.singleton(E.VIDE)))


def pair_neq_impair_cible(a="apni", b="bpni2"):
    va, vb = _t(a), _t(b)
    return impl(et(est_fini(va), est_fini(vb)),
                non(egal(deux_fois(va), successeur(deux_fois(vb)))))


def pair_neq_impair(a="apni", b="bpni2", k="kpni"):
    """🎯 ⊢ (Fini a et Fini b) ⇒ ¬( 2·a = 2·b+1 ).   ( « pair ≠ impair ». )

    Récurrence C61 sur a (Q[a] := ∀b(Fini b ⇒ 2a ≠ succ 2b)) ; base 2·0=0≠succ ;
    pas via prédécesseur de b + successeur injectif (Prop. 8).  theorie=22, 0 hyp."""
    va, vb = _t(a), _t(b)
    P = _Qpni
    p0 = _pni_P0()
    step = _pni_step("apni")
    assert p0.conclusion == P(ZERO), "Q[0] mal formé"
    assert step.conclusion == _fini_et_P_implique_succ(P, "apni"), "pas pni mal formé"

    princ_imp = principe_recurrence_preuve(P, "apni", k=k)
    pfu = predecesseur_fini_universel(k=k)
    assert pfu in princ_imp.hypotheses, "pfu absent"
    princ_imp = _cut(princ_imp, pfu, predecesseur_fini_universel_preuve(k=k))
    ante = conjonction_intro(p0, step)
    fini_implique_Qa = N.modus_ponens(ante, princ_imp)   # (∀a)(Fini a ⇒ Q[a])

    hc = N.assume(et(est_fini(va), est_fini(vb)))
    fa = conjonction_elim_gauche(hc)
    fb = conjonction_elim_droite(hc)
    Qa = N.modus_ponens(fa, instancie(fini_implique_Qa, va))   # Q[a]
    ne = N.modus_ponens(fb, instancie(Qa, vb))                 # ¬(2a=succ 2b)
    res = N.loi_deduction(et(est_fini(va), est_fini(vb)), ne)
    cible = pair_neq_impair_cible(a, b)
    assert res.conclusion == cible, \
        f"pair_neq_impair : conclusion inattendue\n{res.conclusion}\n{cible}"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (3b) « 2k+1 EST IMPAIR » — ¬( 2 | (2k+1) )   et le cas k=0 : ¬( 2 | 1 ).
# ══════════════════════════════════════════════════════════════════════════════
def _pair_neq_impair_t(ta, tb):
    """pair_neq_impair capture-safe : ⊢ (Fini a et Fini b) ⇒ ¬(2·a = succ(2·b))."""
    g = N.generalisation("apnit", N.generalisation("bpnit",
            pair_neq_impair("apnit", "bpnit")))
    return instancie(instancie(g, _t(ta)), _t(tb))


def deux_k_plus_un_impair_cible(k="kdki"):
    vk = _t(k)
    return impl(est_fini(vk), est_impair_propre(successeur(deux_fois(vk))))


def deux_k_plus_un_impair(k="kdki"):
    """🎯 ⊢ est_fini(k) ⇒ ¬( 2 | (2·k+1) ).   ( 2·k+1 := succ(2·k) est IMPAIR. )

    est_impair_propre(succ 2k) = ¬divise_propre(2, succ 2k) = ¬(∃q)(Fini q et succ 2k = 2q).
    Pour un tel q : pair_neq_impair(q, k) ⊢ ¬(2q = succ 2k) ; or succ 2k = 2q (symétrie)
    contredit.  Donc aucun q : ¬divise_propre."""
    vk = _t(k)
    twok = deux_fois(vk)
    succ2k = successeur(twok)

    hfk = N.assume(est_fini(vk))

    # divise_propre(2, succ 2k) = (∃q)(Fini q et succ 2k = produit_cardinal_binaire(2,q))
    vq = var("qdiv")
    corps_q = et(est_fini(vq), egal(succ2k, deux_fois(vq)))
    hq = N.assume(corps_q)
    fini_q = conjonction_elim_gauche(hq)
    eq_q = conjonction_elim_droite(hq)                 # succ 2k = 2q
    # 2q = succ 2k  (symétrie)
    twoq_eq = N.modus_ponens(eq_q, symetrie(succ2k, deux_fois(vq)))   # 2q = succ 2k
    # pair_neq_impair(q,k) : (Fini q et Fini k) ⇒ ¬(2q = succ 2k)
    pni = _pair_neq_impair_t(vq, vk)
    ne = N.modus_ponens(conjonction_intro(fini_q, hfk), pni)   # ¬(2q = succ 2k)
    # contradiction : 2q=succ2k et ¬(2q=succ2k) ⇒ ⊥ ⇒ ¬corps_q
    E = existe("qdiv", corps_q)                        # (∃q)corps_q = divise_propre(2, succ 2k)
    # sous corps_q : contradiction (2q=succ2k vs ¬(2q=succ2k)) ⇒ ¬E
    contra = _ex_falso(twoq_eq, ne, non(E))            # ¬E   [corps_q, Fini k]
    imp = N.loi_deduction(corps_q, contra)             # corps_q ⇒ ¬E
    ex_imp = existe_elimination(imp, "qdiv")           # E ⇒ ¬E
    not_exists = _refute_self(ex_imp)                  # ¬E = est_impair_propre(succ 2k)
    res = N.loi_deduction(est_fini(vk), not_exists)
    cible = deux_k_plus_un_impair_cible(k)
    assert res.conclusion == cible, \
        f"deux_k_plus_un_impair : conclusion inattendue\n{res.conclusion}\n{cible}"
    return res


def un_impair():
    """🎯 ⊢ est_impair_propre(1).   ( ¬( 2 | 1 ). )

    1 = UN = succ(0) = succ(2·0)  (2·0 = 0).  deux_k_plus_un_impair(0) ⊢
    ¬(2 | succ(2·0)) ; Fini 0 ; Leibniz succ(2·0)=1 transporte en ¬(2|1)."""
    from bourbaki.entiers.ensembles_fini_zero import fini_zero
    dki = N.modus_ponens(fini_zero(), deux_k_plus_un_impair(ZERO))   # ¬(2 | succ(2·0))
    # succ(2·0) = succ(0) = UN   (2·0 = 0 ⇒ succ(2·0)=succ(0)=1)
    eq20 = _deux_fois_zero_eq()                         # 2·0 = 0
    eq_succ = _congr_succ(eq20)                         # succ(2·0) = succ(0) = UN
    #   successeur(ZERO) == UN littéralement.
    # transporte : ¬(2|succ 2·0) ⇒ ¬(2|UN)  (Leibniz succ(2·0)=UN sur est_impair_propre)
    leib = N.modus_ponens(eq_succ,
        N.s6(successeur(deux_fois(ZERO)), UN, "wui", est_impair_propre(var("wui"))))
    res = N.modus_ponens(dki, equivalence_avant(leib))  # est_impair_propre(UN)
    assert res.conclusion == est_impair_propre(UN), \
        f"un_impair : conclusion inattendue\n{res.conclusion}\n{est_impair_propre(UN)}"
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (3c) PRODUIT DE DEUX IMPAIRS EST IMPAIR.
#       a=succ(2i), b=succ(2j) ⇒ a·b = succ( 2·(a·j + i) ), donc impair.
# ══════════════════════════════════════════════════════════════════════════════
def _comm_prod_t(tx, ty):
    """⊢ Card(x×y) = Card(y×x)   (= x·y = y·x au niveau cardinaux), capture-safe."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
        produit_cardinal_commutatif,
    )
    g = produit_cardinal_commutatif("Xcpt", "Ycpt")
    gen = N.generalisation("Xcpt", N.generalisation("Ycpt", g))
    return instancie(instancie(gen, _t(tx)), _t(ty))


def _produit_cardinal_un_t2(ta):
    from bourbaki.cardinaux.arithmetique.ensembles_produit_petits import produit_cardinal_un
    gen = N.generalisation("Apcu2", produit_cardinal_un("Apcu2"))
    return instancie(gen, _t(ta))


def _distrib_droite_t(ta, td, tc):
    """⊢ (Fini a et Fini d et Fini c) ⇒ (a+d)·c = a·c + d·c   (capture-safe).

    Réutilise _distrib_droite (prop3_strict_mono) qui exige les preuves est_cardinal ;
    on les fournit depuis Fini (conjonction_elim_gauche)."""
    from bourbaki.entiers.ensembles_prop3_strict_mono_iii5 import _distrib_droite
    va, vd, vc = _t(ta), _t(td), _t(tc)
    ha = N.assume(et(et(est_fini(va), est_fini(vd)), est_fini(vc)))
    fa = conjonction_elim_gauche(conjonction_elim_gauche(ha))
    fd = conjonction_elim_droite(conjonction_elim_gauche(ha))
    fc = conjonction_elim_droite(ha)
    ca = conjonction_elim_gauche(fa)
    cd = conjonction_elim_gauche(fd)
    cc = conjonction_elim_gauche(fc)
    dd = _distrib_droite(va, vd, vc, ca, cd, cc)   # (a+d)·c = a·c + d·c
    return N.loi_deduction(et(et(est_fini(va), est_fini(vd)), est_fini(vc)), dd)


def _prod_assoc_t(tx, ty, tz):
    """⊢ Card((x×y)×z) = Card(x×(y×z))   capture-safe."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
        produit_cardinal_associatif,
    )
    g = produit_cardinal_associatif("Xpat", "Ypat", "Zpat")
    gen = N.generalisation("Xpat", N.generalisation("Ypat",
          N.generalisation("Zpat", g)))
    return instancie(instancie(instancie(gen, _t(tx)), _t(ty)), _t(tz))


def _pcbd_t(tX, tY, ta, tb):
    """produit_cardinal_bien_defini capture-safe :
       ⊢ (Card X=a et Card Y=b) ⇒ Card(X×Y) = produit_cardinal_binaire(a,b)."""
    from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import (
        produit_cardinal_bien_defini,
    )
    g = produit_cardinal_bien_defini("Xpcb", "Ypcb", "apcb", "bpcb")
    gen = N.generalisation("Xpcb", N.generalisation("Ypcb",
          N.generalisation("apcb", N.generalisation("bpcb", g))))
    return instancie(instancie(instancie(instancie(gen, _t(tX)), _t(tY)),
                     _t(ta)), _t(tb))


def _a_2j_eq_2_aj(a, j):
    """⊢ (Fini a et Fini j) ⇒ a·(2·j) = 2·(a·j).

    Chaîne (cardinaux, invariance ponts) :
      a·(2j) = Card(a×(2×j))        [pont : 2j=Card(2×j), bien_defini]
             = Card((a×2)×j)        [associativité symétrisée]
             = (a·2)·j              [pont : a·2=Card(a×2), j=Card(j) ; bien_defini]
      a·2 = 2·a (commut) ⇒ (a·2)·j = (2·a)·j   [congruence à gauche du produit]
      (2·a)·j = 2·(a·j) : symétrique du même schéma (assoc + ponts) avec (2,a,j)."""
    va, vj = _t(a), _t(j)
    hfin = N.assume(et(est_fini(va), est_fini(vj)))
    fa = conjonction_elim_gauche(hfin)
    fj = conjonction_elim_droite(hfin)
    ca = conjonction_elim_gauche(fa)               # card a
    cj = conjonction_elim_gauche(fj)               # card j
    card_a = N.modus_ponens(ca, _card_de_card_t(va))   # Card a = a
    card_j = N.modus_ponens(cj, _card_de_card_t(vj))   # Card j = j

    twoj = deux_fois(vj)                            # 2·j = Card(2×j)
    twoa = deux_fois(va)                            # 2·a = Card(2×a)
    a2 = produit_cardinal_binaire(va, DEUX)         # a·2 = Card(a×2)
    aj = produit_cardinal_binaire(va, vj)           # a·j

    # ── a·(2j) = Card(a×(2×j)) ──────────────────────────────────────────────
    # bien_defini(a, 2×j, a, 2j) : (Card a=a et Card(2×j)=2j) ⇒ Card(a×(2×j))=a·(2j)
    set_2j = E.produit(DEUX, vj)                    # 2×j
    refl_2j = N.reflexivite(twoj)                   # Card(2×j) = 2j  (twoj == Card(2×j))
    bd1 = _pcbd_t(va, set_2j, va, twoj)
    eq1 = N.modus_ponens(conjonction_intro(card_a, refl_2j), bd1)   # Card(a×(2×j)) = a·(2j)
    a_2j = produit_cardinal_binaire(va, twoj)       # a·(2j)
    Card_a_2j = cardinal(E.produit(va, set_2j))
    eq1s = N.modus_ponens(eq1, symetrie(Card_a_2j, a_2j))   # a·(2j) = Card(a×(2×j))

    # ── Card(a×(2×j)) = Card((a×2)×j)  (assoc symétrisée) ───────────────────
    assoc = _prod_assoc_t(va, DEUX, vj)             # Card((a×2)×j) = Card(a×(2×j))
    set_a2 = E.produit(va, DEUX)
    Card_a2_j = cardinal(E.produit(set_a2, vj))
    assoc_s = N.modus_ponens(assoc, symetrie(Card_a2_j, Card_a_2j))  # Card(a×(2×j))=Card((a×2)×j)

    # ── Card((a×2)×j) = (a·2)·j  (bien_defini : Card(a×2)=a·2, Card j=j) ─────
    refl_a2 = N.reflexivite(a2)                     # Card(a×2)=a·2  (a2==Card(a×2))
    bd2 = _pcbd_t(set_a2, vj, a2, vj)
    eq3 = N.modus_ponens(conjonction_intro(refl_a2, card_j), bd2)   # Card((a×2)×j) = (a·2)·j

    # a·(2j) = Card(a×(2×j)) = Card((a×2)×j) = (a·2)·j
    chainL = composer_egalites(composer_egalites(eq1s, assoc_s), eq3)   # a·(2j) = (a·2)·j

    # ── (a·2)·j = (2·a)·j  : a·2 = 2·a (commut) congruence à gauche ─────────
    comm_a2 = _comm_prod_t(va, DEUX)                # Card(a×2)=Card(2×a)  = a·2 = 2·a
    #   a·2 == Card(a×2) ; 2·a == Card(2×a)  (déf)
    a2j = produit_cardinal_binaire(a2, vj)          # (a·2)·j
    twoa_j = produit_cardinal_binaire(twoa, vj)     # (2·a)·j
    leibG = N.modus_ponens(comm_a2,
        N.s6(a2, twoa, "wfg", egal(a2j, produit_cardinal_binaire(var("wfg"), vj))))
    eqG = N.modus_ponens(N.reflexivite(a2j), equivalence_avant(leibG))   # (a·2)·j = (2·a)·j

    # ── (2·a)·j = 2·(a·j)  : assoc (2,a,j) + ponts (miroir) ─────────────────
    # Card((2×a)×j) = Card(2×(a×j)) ; (2·a)·j = Card((2×a)×j) [bien_defini], 2·(a·j) = Card(2×(a×j))
    set_2a = E.produit(DEUX, va)
    refl_2a = N.reflexivite(twoa)                   # Card(2×a)=2·a
    bd3 = _pcbd_t(set_2a, vj, twoa, vj)
    eq4 = N.modus_ponens(conjonction_intro(refl_2a, card_j), bd3)   # Card((2×a)×j) = (2·a)·j
    Card_2a_j = cardinal(E.produit(set_2a, vj))
    eq4s = N.modus_ponens(eq4, symetrie(Card_2a_j, twoa_j))         # (2·a)·j = Card((2×a)×j)
    assoc2 = _prod_assoc_t(DEUX, va, vj)            # Card((2×a)×j) = Card(2×(a×j))
    # Card(2×(a×j)) = 2·(a·j)  (bien_defini : Card 2=2, Card(a×j)=a·j)
    card_2 = N.modus_ponens(deux_est_un_cardinal(), _card_de_card_t(DEUX))   # Card 2 = 2
    refl_aj = N.reflexivite(aj)                     # Card(a×j) = a·j
    set_aj = E.produit(va, vj)
    bd4 = _pcbd_t(DEUX, set_aj, DEUX, aj)
    eq5 = N.modus_ponens(conjonction_intro(card_2, refl_aj), bd4)   # Card(2×(a×j)) = 2·(a·j)
    chainR = composer_egalites(composer_egalites(eq4s, assoc2), eq5)   # (2·a)·j = 2·(a·j)

    # ── ASSEMBLAGE : a·(2j) = (a·2)·j = (2·a)·j = 2·(a·j) ───────────────────
    final = composer_egalites(composer_egalites(chainL, eqG), chainR)   # a·(2j) = 2·(a·j)
    return N.loi_deduction(et(est_fini(va), est_fini(vj)), final)


def _deux_distrib(x, y):
    """⊢ (Fini x et Fini y) ⇒ 2·(x+y) = 2·x + 2·y.

    2·(x+y) = (x+y)·2  [commut]
            = x·2 + y·2  [_distrib_droite(x,y,2)]
            = 2·x + 2·y  [commut × 2]."""
    vx, vy = _t(x), _t(y)
    hfin = N.assume(et(est_fini(vx), est_fini(vy)))
    fx = conjonction_elim_gauche(hfin)
    fy = conjonction_elim_droite(hfin)
    cx = conjonction_elim_gauche(fx)
    cy = conjonction_elim_gauche(fy)
    card_x = N.modus_ponens(cx, _card_de_card_t(vx))
    card_y = N.modus_ponens(cy, _card_de_card_t(vy))

    xy = somme_cardinale_binaire(vx, vy)            # x+y
    # 2·(x+y) = (x+y)·2   (commut produit ; déf : 2·(x+y)=Card(2×(x+y)), (x+y)·2=Card((x+y)×2))
    comm0 = _comm_prod_t(DEUX, xy)                  # Card(2×(x+y)) = Card((x+y)×2)  = 2·(x+y)=(x+y)·2
    two_xy = deux_fois(xy)                          # 2·(x+y)
    xy_two = produit_cardinal_binaire(xy, DEUX)     # (x+y)·2
    # (x+y)·2 = x·2 + y·2   (_distrib_droite(x,y,2) sous Fini x,y,2)
    from bourbaki.entiers.ensembles_fini_deux import fini_deux
    dd = _distrib_droite_t(vx, vy, DEUX)            # (Fini x et Fini y et Fini 2)⇒ (x+y)·2 = x·2+y·2
    dd2 = N.modus_ponens(conjonction_intro(conjonction_intro(fx, fy), fini_deux()), dd)
    x2 = produit_cardinal_binaire(vx, DEUX)         # x·2
    y2 = produit_cardinal_binaire(vy, DEUX)         # y·2
    # x·2 = 2·x, y·2 = 2·y  (commut)
    comm_x = _comm_prod_t(vx, DEUX)                 # Card(x×2)=Card(2×x) = x·2=2·x
    comm_y = _comm_prod_t(vy, DEUX)                 # y·2=2·y
    twox = deux_fois(vx)
    twoy = deux_fois(vy)
    # remplacer x·2 -> 2·x dans (w + y·2)
    Vl = somme_cardinale_binaire(var("wddl"), y2)
    sx = N.modus_ponens(comm_x, congruence_terme(x2, twox, Vl, w="wddl"))   # x·2+y·2 = 2·x+y·2
    Vr = somme_cardinale_binaire(twox, var("wddr"))
    sy = N.modus_ponens(comm_y, congruence_terme(y2, twoy, Vr, w="wddr"))   # 2·x+y·2 = 2·x+2·y
    sxy = composer_egalites(sx, sy)                 # x·2+y·2 = 2·x+2·y
    # 2·(x+y) = (x+y)·2 = x·2+y·2 = 2·x+2·y
    chain = composer_egalites(composer_egalites(comm0, dd2), sxy)
    return N.loi_deduction(et(est_fini(vx), est_fini(vy)), chain)


def _somme_succ_distribue_t2(ta, tb):
    g = somme_succ_distribue("assd2", "bssd2")
    gen = N.generalisation("assd2", N.generalisation("bssd2", g))
    return instancie(instancie(gen, _t(ta)), _t(tb))


def _produit_succ_distribue_t2(ta, tn):
    g = produit_succ_distribue("apsd2", "npsd2")
    gen = N.generalisation("apsd2", N.generalisation("npsd2", g))
    return instancie(instancie(gen, _t(ta)), _t(tn))


def _somme_binaire_entier_t(x, y):
    from bourbaki.entiers.ensembles_combinatoire_iii5 import somme_binaire_entier
    g = N.generalisation("xsbe2", N.generalisation("ysbe2",
            somme_binaire_entier("xsbe2", "ysbe2")))
    return instancie(instancie(g, _t(x)), _t(y))


def _produit_binaire_entier_t(x, y):
    from bourbaki.entiers.ensembles_prop3_produit_entier_iii5 import produit_binaire_entier
    g = N.generalisation("xpbe2", N.generalisation("ypbe2",
            produit_binaire_entier("xpbe2", "ypbe2")))
    return instancie(instancie(g, _t(x)), _t(y))


def impair_fois_impair_cible(a="aifi", b="bifi"):
    va, vb = _t(a), _t(b)
    return impl(et(et(est_fini(va), est_fini(vb)),
                   et(est_impair_propre(va), est_impair_propre(vb))),
                est_impair_propre(produit_cardinal_binaire(va, vb)))


def _afi_eq_succ2M(va, vi, vj, fa, fi, fj, a_eq, b_eq):
    """De preuves { Fini a [fa], Fini i [fi], Fini j [fj], a=succ(2i) [a_eq],
       b=succ(2j) [b_eq] } déduit  ⊢ a·b = succ( 2·(a·j + i) ).   (b = succ(2j).)"""
    twoi = deux_fois(vi)
    twoj = deux_fois(vj)
    aj = produit_cardinal_binaire(va, vj)           # a·j
    a_2j = produit_cardinal_binaire(va, twoj)       # a·(2j)
    ca = conjonction_elim_gauche(fa)                # card a

    # a·b : b = succ(2j) ⇒ a·b = a·succ(2j)  (Leibniz b→succ 2j sur a·•)
    vb_term = successeur(twoj)                       # succ(2j) (= b)
    # a·succ(2j) = a·(2j) + a   (produit_succ_distribue(a,2j) ; card a, card 2j)
    card_2j = _est_cardinal_produit(DEUX, vj)
    psd = N.modus_ponens(conjonction_intro(ca, card_2j), _produit_succ_distribue_t2(va, twoj))
    #   psd : a·succ(2j) = a·(2j) + a
    # transporte b→succ 2j : a·b = a·succ(2j).  On part de psd, réécrit a·succ(2j) en a·b.
    # b_eq : a is fixed; need b=succ(2j) to write a·b = a·succ(2j). On garde la forme succ(2j)
    # et substitue à la FIN (a·b apparait via Leibniz sur b). On travaille en succ(2j) puis
    # remplace par b.
    sum_a2j_a = somme_cardinale_binaire(a_2j, va)   # a·(2j)+a

    # a·(2j)+a = a·(2j)+succ(2i)   (a=succ(2i) ⇒ remplace a par succ(2i) à droite de +)
    Vrep = somme_cardinale_binaire(a_2j, var("wifa"))
    rep_a = N.modus_ponens(a_eq, congruence_terme(va, successeur(twoi), Vrep, w="wifa"))
    #   rep_a : a·(2j)+a = a·(2j)+succ(2i)
    sum_a2j_succ2i = somme_cardinale_binaire(a_2j, successeur(twoi))

    # a·(2j)+succ(2i) = succ( a·(2j)+2i )   (somme_succ_distribue(a·2j, 2i) ; card a2j, card 2i)
    card_a2j = _est_cardinal_produit(va, twoj)
    card_2i = _est_cardinal_produit(DEUX, vi)
    ssd = N.modus_ponens(conjonction_intro(card_a2j, card_2i),
                         _somme_succ_distribue_t2(a_2j, twoi))
    #   ssd : a·(2j)+succ(2i) = succ( a·(2j)+2i )

    # a·(2j) = 2·(a·j)  (H1) ⇒ remplace dans succ( w + 2i )
    h1 = N.modus_ponens(conjonction_intro(fa, fj), _a_2j_eq_2_aj(va, vj))   # a·(2j)=2·(a·j)
    two_aj = deux_fois(aj)                           # 2·(a·j)
    Vh1 = successeur(somme_cardinale_binaire(var("wh1"), twoi))
    rep_h1 = N.modus_ponens(h1, congruence_terme(a_2j, two_aj, Vh1, w="wh1"))
    #   rep_h1 : succ(a·(2j)+2i) = succ(2·(a·j)+2i)
    succ_2aj_2i = successeur(somme_cardinale_binaire(two_aj, twoi))

    # 2·(a·j)+2·i = 2·(a·j+i)  (H2 _deux_distrib(a·j, i)) ⇒ remplace dans succ(•)
    fini_aj = N.modus_ponens(conjonction_intro(fa, fj), _produit_binaire_entier_t(va, vj))  # Fini(a·j)
    h2_raw = N.modus_ponens(conjonction_intro(fini_aj, fi), _deux_distrib(aj, vi))   # 2·(aj+i) = 2·(aj)+2·i
    aj_i = somme_cardinale_binaire(aj, vi)          # a·j + i
    two_ajpi = deux_fois(aj_i)                       # 2·(a·j+i)
    sum_2aj_2i = somme_cardinale_binaire(two_aj, twoi)   # 2·(aj)+2·i
    h2 = N.modus_ponens(h2_raw, symetrie(two_ajpi, sum_2aj_2i))   # 2·(aj)+2·i = 2·(aj+i)
    Vh2 = successeur(var("wh2"))
    rep_h2 = N.modus_ponens(h2, congruence_terme(sum_2aj_2i, two_ajpi, Vh2, w="wh2"))
    #   rep_h2 : succ(2·(a·j)+2·i) = succ(2·(a·j+i))

    # ASSEMBLAGE : a·succ(2j) = a·(2j)+a = a·(2j)+succ(2i) = succ(a·2j+2i)
    #            = succ(2·(a·j)+2i) = succ(2·(a·j+i))
    chain = composer_egalites(
              composer_egalites(
                composer_egalites(composer_egalites(psd, rep_a), ssd),
                rep_h1),
              rep_h2)                                # a·succ(2j) = succ(2·(a·j+i))
    return chain, aj_i      # chain : a·succ(2j) = succ(2·(a·j+i)) ;  M = a·j+i


def impair_fois_impair(a="aifi", b="bifi"):
    """🎯 ⊢ (Fini a et Fini b et impair a et impair b) ⇒ impair( a·b ).

    a=succ(2i), b=succ(2j) (impair_decompose) ; a·b = succ(2·(a·j+i)) =: succ(2·M),
    M = a·j+i fini ; deux_k_plus_un_impair(M) ⊢ impair(succ 2M) = impair(a·b)."""
    va, vb = _t(a), _t(b)
    hyp = N.assume(et(et(est_fini(va), est_fini(vb)),
                      et(est_impair_propre(va), est_impair_propre(vb))))
    fab = conjonction_elim_gauche(hyp)
    fa = conjonction_elim_gauche(fab)
    fb = conjonction_elim_droite(fab)
    imp = conjonction_elim_droite(hyp)
    impa = conjonction_elim_gauche(imp)
    impb = conjonction_elim_droite(imp)

    cible = est_impair_propre(produit_cardinal_binaire(va, vb))

    # impair_decompose(a) ⇒ ∃kid (Fini kid et a=succ 2kid) ; idem b. α-renomme kid→iifi/jifi.
    from bourbaki.logique.tactiques.tactiques_abrege_quantif import alpha_existe
    deca0 = N.modus_ponens(conjonction_intro(fa, impa), impair_decompose(a))
    decb0 = N.modus_ponens(conjonction_intro(fb, impb), impair_decompose(b))
    body_a = et(est_fini(var("kid")), egal(va, successeur(deux_fois(var("kid")))))
    body_b = et(est_fini(var("kid")), egal(vb, successeur(deux_fois(var("kid")))))
    deca = N.modus_ponens(deca0, equivalence_avant(alpha_existe("kid", "iifi", body_a)))
    decb = N.modus_ponens(decb0, equivalence_avant(alpha_existe("kid", "jifi", body_b)))

    vi = var("iifi")
    vj = var("jifi")
    corps_i = et(est_fini(vi), egal(va, successeur(deux_fois(vi))))
    corps_j = et(est_fini(vj), egal(vb, successeur(deux_fois(vj))))
    hI = N.assume(corps_i)
    fi = conjonction_elim_gauche(hI)
    a_eq = conjonction_elim_droite(hI)              # a = succ(2i)
    hJ = N.assume(corps_j)
    fj = conjonction_elim_gauche(hJ)
    b_eq = conjonction_elim_droite(hJ)              # b = succ(2j)

    chain, M = _afi_eq_succ2M(va, vi, vj, fa, fi, fj, a_eq, b_eq)
    #   chain : a·succ(2j) = succ(2·M)

    # a·b = a·succ(2j)  (b = succ 2j ⇒ Leibniz sur 2e arg du produit)
    Vab = produit_cardinal_binaire(va, var("wab"))
    ab_eq = N.modus_ponens(b_eq, congruence_terme(vb, successeur(deux_fois(vj)), Vab, w="wab"))
    #   ab_eq : a·b = a·succ(2j)
    ab_eq_succ2M = composer_egalites(ab_eq, chain)   # a·b = succ(2·M)

    # M = a·j + i fini : Fini(a·j) (produit) + Fini i ⇒ Fini(a·j+i)
    fini_aj = N.modus_ponens(conjonction_intro(fa, fj), _produit_binaire_entier_t(va, vj))
    fini_M = N.modus_ponens(conjonction_intro(fini_aj, fi), _somme_binaire_entier_t(
        produit_cardinal_binaire(va, vj), vi))       # Fini(a·j+i) = Fini M
    # deux_k_plus_un_impair(M) : Fini M ⇒ impair(succ 2M)
    dki = instancie(N.generalisation("kdki_g", deux_k_plus_un_impair("kdki_g")), M)
    impair_succ2M = N.modus_ponens(fini_M, dki)      # impair(succ 2M)
    # transporte succ 2M → a·b  (a·b = succ 2M ⇒ Leibniz)
    succ2M = successeur(deux_fois(M))
    ab_term = produit_cardinal_binaire(va, vb)
    succ2M_eq_ab = N.modus_ponens(ab_eq_succ2M, symetrie(ab_term, succ2M))   # succ 2M = a·b
    leib = N.modus_ponens(succ2M_eq_ab,
        N.s6(succ2M, ab_term, "wfi", est_impair_propre(var("wfi"))))   # (succ2M=a·b)⇒(imp(succ2M)⇔imp(a·b))
    impair_ab = N.modus_ponens(impair_succ2M, equivalence_avant(leib))   # impair(a·b)

    # élimine j puis i
    imp_j = N.loi_deduction(corps_j, impair_ab)
    ex_j = existe_elimination(imp_j, "jifi")         # (∃j corps_j) ⇒ impair(a·b)
    impair_ab_i = N.modus_ponens(decb, ex_j)         # impair(a·b)   [corps_i, ...]
    imp_i = N.loi_deduction(corps_i, impair_ab_i)
    ex_i = existe_elimination(imp_i, "iifi")
    impair_ab_final = N.modus_ponens(deca, ex_i)     # impair(a·b)
    res = N.loi_deduction(et(et(est_fini(va), est_fini(vb)),
                             et(est_impair_propre(va), est_impair_propre(vb))),
                          impair_ab_final)
    assert res.conclusion == impair_fois_impair_cible(a, b), \
        f"impair_fois_impair : conclusion inattendue\n{res.conclusion}\n{impair_fois_impair_cible(a,b)}"
    return res


__all__ = [
    "deux_fois", "deux_fois_plus_un", "deux_succ_eq",
    "division_par_deux", "division_par_deux_cible",
    "impair_decompose", "impair_decompose_cible",
    "pair_neq_impair", "pair_neq_impair_cible",
    "deux_k_plus_un_impair", "deux_k_plus_un_impair_cible", "un_impair",
    "impair_fois_impair", "impair_fois_impair_cible",
]
