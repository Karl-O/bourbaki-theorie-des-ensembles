"""§III.4 — SOUS-LEMME DE LA « PIGEONHOLE » (cœur du Cor. 2 §III.4).

🎯  partie_egal_cardinal_egal :
        ⊢ ( X⊂E et est_fini_ensemble(E) et Card(X) = Card(E) ) ⇒ X = E.

« Un sous-ensemble d'un ensemble FINI ayant le MÊME cardinal est l'ensemble
entier. »  C'est le cœur combinatoire du principe des tiroirs (Cor. 2 §III.4).

ROUTE (entièrement à partir de briques CLOSES) :
  1. E = X ∪ (E∖X)  (partie_reunion_complement, sous X⊂E) et X ∩ (E∖X) = ∅
     (partie_disjoint_complement) ;
  2. X et E∖X finis (partie_finie_est_finie ; E∖X⊂E) ;
  3. Card E = Card X + Card(E∖X) :  Eq(X∪(E∖X), X⊔(E∖X)) (eq_reunion_disjointe_somme,
     sous disjonction) ⇒ Card(X∪(E∖X)) = Card(X⊔(E∖X)) (Prop. 1) ; réécriture
     X∪(E∖X)=E ⇒ Card E = Card(X⊔(E∖X)) = Card X + Card(E∖X) (somme_disjointe_cardinal) ;
  4. de Card X = Card E :  Card X + Card(E∖X) = Card X = Card X + 0
     (somme_zero_neutre_droite) ⇒ par simplification_additive_finie(Card X)
     (Card X entier car X fini) : Card(E∖X) = 0 ;
  5. Card(E∖X) = 0 ⇒ E∖X = ∅ (cardinal_egal_zero_ssi_vide) ;
  6. E = X∪(E∖X) = X∪∅ = X (reunion_vide_neutre) ⇒ X = E.

⚠ INVARIANT : theorie_ensembles() = 22.  Rien postulé.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E

from bourbaki.cardinaux.ensembles_cardinaux import est_cardinal, cardinal, inf_strict_card
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini_ensemble, est_entier, ZERO
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire,
)

from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, instancie,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)

# ── briques CLOSES réutilisées ────────────────────────────────────────────────
from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import (
    partie_reunion_complement, partie_disjoint_complement,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_recurrence_c61_existence_n.ensembles_predecesseur_prop2 import eq_reunion_disjointe_somme
from bourbaki.cardinaux.arithmetique.iii_3_3_somme.ensembles_arith_somme import _prop1_direct_t
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_combinatoire_iii5 import somme_zero_neutre_droite, _sdc
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_1_somme_produit_entiers.ensembles_simplification_additive import simplification_additive_finie
from bourbaki.cardinaux.ensembles_cardinaux_props_restantes_prop7 import (
    cardinal_egal_zero_ssi_vide,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop6_bien_ordonne_iii5 import partie_finie_est_finie
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_vide_identites import reunion_vide_neutre


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
#  inclusion E∖X ⊂ E  (le complément d'une partie est une partie)
# ════════════════════════════════════════════════════════════════════════════
def _diff_inclus(tE, tX, w="z"):
    """⊢ (E∖X) ⊂ E.    z∈E∖X ⇒ (z∈E et ¬z∈X) ⇒ z∈E.  (binder « z » aligné sur inclus.)"""
    from bourbaki.logique.i_1_termes_relations.formule import appartient, impl, non, inclus
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import projection_gauche, syllogisme
    from bourbaki.logique.i_1_termes_relations.formule import libres_t
    # choix du binder identique à inclus(E∖X, E)
    EmX = E.difference(tE, tX)
    if w in libres_t(EmX) | libres_t(tE):
        from bourbaki.logique.i_1_termes_relations.formule import _fraiche
        w = _fraiche(libres_t(EmX) | libres_t(tE))
    vw = var(w)
    from bourbaki.cardinaux.ensembles_cantor_bernstein_fin import _inst_diff
    carD = _inst_diff(tE, tX, vw)                          # z∈E∖X ⇔ (z∈E et ¬z∈X)
    br = syllogisme(equivalence_avant(carD),
                    projection_gauche(appartient(vw, tE), non(appartient(vw, tX))))  # z∈E∖X ⇒ z∈E
    res = N.generalisation(w, br)                          # (E∖X) ⊂ E
    assert res.conclusion == inclus(EmX, tE), "diff_inclus ≠ inclus(E∖X,E)"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 SOUS-LEMME
# ════════════════════════════════════════════════════════════════════════════
def partie_egal_cardinal_egal_enonce(X="Xpe", Eens="Epe"):
    """⊢-cible : ( X⊂E et est_fini_ensemble(E) et Card X = Card E ) ⇒ X = E."""
    from bourbaki.logique.i_1_termes_relations.formule import impl, inclus
    vX, vE = _t(X), _t(Eens)
    ante = et(et(inclus(vX, vE), est_fini_ensemble(vE)),
              egal(cardinal(vX), cardinal(vE)))
    return impl(ante, egal(vX, vE))


def partie_egal_cardinal_egal(X="Xpe", Eens="Epe"):
    """🎯🎯 ⊢ ( X⊂E et est_fini_ensemble(E) et Card X = Card E ) ⇒ X = E.   (CLOS, 0 hyp.)

    Cœur de la pigeonhole (Cor. 2 §III.4).  Voir docstring de module pour la route."""
    from bourbaki.logique.i_1_termes_relations.formule import impl, inclus
    vX, vE = _t(X), _t(Eens)
    incl = inclus(vX, vE)
    EmX = E.difference(vE, vX)                              # E∖X
    cX, cE, cD = cardinal(vX), cardinal(vE), cardinal(EmX)
    reun = E.reunion(vX, EmX)                               # X ∪ (E∖X)
    somdisj = somme_disjointe(vX, EmX)                      # X ⊔ (E∖X)

    ante = et(et(incl, est_fini_ensemble(vE)), egal(cX, cE))
    h = N.assume(ante)
    h_incl = conjonction_elim_gauche(conjonction_elim_gauche(h))     # X⊂E
    h_Efini = conjonction_elim_droite(conjonction_elim_gauche(h))    # est_fini_ensemble(E)
    h_card = conjonction_elim_droite(h)                              # Card X = Card E

    # ── (1) E = X∪(E∖X)  et  X∩(E∖X)=∅ ──────────────────────────────────────
    E_eq_reun = N.modus_ponens(h_incl, partie_reunion_complement(vE, vX))  # X∪(E∖X) = E
    assert E_eq_reun.conclusion == egal(reun, vE), "E_eq_reun ≠ (X∪(E∖X)=E)"
    disj = partie_disjoint_complement(vE, vX)               # X∩(E∖X) = ∅   (clos)
    from bourbaki.logique.i_1_termes_relations.formule import appartient   # noqa
    assert disj.est_clos

    # ── (2) X fini, E∖X fini ────────────────────────────────────────────────
    X_fini = N.modus_ponens(conjonction_intro(h_incl, h_Efini), partie_finie_est_finie(vX, vE))
    assert X_fini.conclusion == est_fini_ensemble(vX)
    D_incl = _diff_inclus(vE, vX)                           # (E∖X)⊂E
    D_fini = N.modus_ponens(conjonction_intro(D_incl, h_Efini), partie_finie_est_finie(EmX, vE))
    assert D_fini.conclusion == est_fini_ensemble(EmX)

    # ── (3) Card E = Card X + Card(E∖X) ─────────────────────────────────────
    # Eq(X∪(E∖X), X⊔(E∖X))  sous X∩(E∖X)=∅
    eq_reun_som_impl = eq_reunion_disjointe_somme(vX, EmX)  # (X∩(E∖X)=∅) ⇒ Eq(X∪(E∖X), X⊔(E∖X))
    eq_reun_som = N.modus_ponens(disj, eq_reun_som_impl)    # Eq(X∪(E∖X), X⊔(E∖X))
    # Card(X∪(E∖X)) = Card(X⊔(E∖X))
    card_reun_eq = N.modus_ponens(eq_reun_som, _prop1_direct_t(reun, somdisj))
    assert card_reun_eq.conclusion == egal(cardinal(reun), cardinal(somdisj))
    # Card(X⊔(E∖X)) = Card X + Card(E∖X)   via somme_disjointe_cardinal(X, E∖X, Card X, Card(E∖X))
    sdc = _sdc(vX, EmX, cX, cD)                            # (Card X=Card X et Card(E∖X)=Card(E∖X)) ⇒ Card(X⊔(E∖X))=CardX+Card(E∖X)
    sdc_ante = conjonction_intro(N.reflexivite(cX), N.reflexivite(cD))
    card_som_eq = N.modus_ponens(sdc_ante, sdc)             # Card(X⊔(E∖X)) = Card X + Card(E∖X)
    cXpD = somme_cardinale_binaire(cX, cD)
    assert card_som_eq.conclusion == egal(cardinal(somdisj), cXpD)
    # Card(X∪(E∖X)) = Card X + Card(E∖X)
    card_reun_to_sum = composer_egalites(card_reun_eq, card_som_eq)   # Card(X∪(E∖X)) = CardX+Card(E∖X)
    # Card E = Card(X∪(E∖X))   via E = X∪(E∖X)  (congruence du cardinal)
    reun_eq_E_sym = symetrie(reun, vE)                     # (X∪(E∖X)=E) ⇒ (E=X∪(E∖X)) ... it's impl
    E_eq_reun_rev = N.modus_ponens(E_eq_reun, reun_eq_E_sym)   # E = X∪(E∖X)
    cardE_eq_cardReun = N.modus_ponens(
        E_eq_reun_rev, congruence_terme(vE, reun, cardinal(var("w")), w="w"))  # Card E = Card(X∪(E∖X))
    assert cardE_eq_cardReun.conclusion == egal(cE, cardinal(reun))
    cardE_eq_sum = composer_egalites(cardE_eq_cardReun, card_reun_to_sum)  # Card E = Card X + Card(E∖X)
    assert cardE_eq_sum.conclusion == egal(cE, cXpD)

    # ── (4) Card(E∖X) = 0 ───────────────────────────────────────────────────
    # Card X = Card X + Card(E∖X) :  Card X = Card E = CardX+Card(E∖X)
    cardX_eq_sum = composer_egalites(h_card, cardE_eq_sum)  # Card X = Card X + Card(E∖X)
    # Card X = Card X + 0  via a+0=a (somme_zero_neutre_droite), Card X cardinal
    card_cardX = _est_cardinal_du_cardinal(vX)              # est_cardinal(Card X)
    # somme_zero_neutre_droite a un binder NAME interne (τ-capture sur cX) :
    # on généralise sur un nom frais puis on instancie au TERME cX.
    szn_gen = N.generalisation("aSZN", somme_zero_neutre_droite("aSZN"))
    szn_cX = instancie(szn_gen, cX)                         # est_cardinal(CardX) ⇒ CardX+0 = Card X
    a_plus_0_eq_a = N.modus_ponens(card_cardX, szn_cX)      # CardX+0 = Card X
    cX_p0 = somme_cardinale_binaire(cX, ZERO)
    assert a_plus_0_eq_a.conclusion == egal(cX_p0, cX)
    cardX_eq_p0 = N.modus_ponens(a_plus_0_eq_a, symetrie(cX_p0, cX))   # Card X = CardX+0
    # CardX+Card(E∖X) = CardX+0 :  = Card X = CardX+0
    sum_eq_p0 = composer_egalites(symetrie_thm(cardX_eq_sum), cardX_eq_p0)  # CardX+Card(E∖X) = CardX+0
    assert sum_eq_p0.conclusion == egal(cXpD, cX_p0)

    # simplification_additive_finie(Card X) : est_entier(Card X) ⇒ (∀c)(∀c')(...)
    # simplification_additive_finie a un binder NAME « aSA » (récurrence) :
    # construire ⊢ est_entier(aSA) ⇒ P(aSA), généraliser, instancier au TERME cX.
    simp_gen = N.generalisation("aSA", simplification_additive_finie("aSA"))
    simp = instancie(simp_gen, cX)                          # est_entier(CardX) ⇒ P(CardX)
    # est_entier(Card X) = est_fini(Card X) = est_fini_ensemble(X)
    P_cardX = N.modus_ponens(_entier_de_fini_ensemble(X_fini, vX), simp)   # P(Card X)
    # instancie c:=Card(E∖X), c':=0
    P_inst = instancie(instancie(P_cardX, cD), ZERO)       # (card Card(E∖X) et card 0 et CardX+Card(E∖X)=CardX+0) ⇒ Card(E∖X)=0
    # antécédent
    card_cD = _est_cardinal_du_cardinal(EmX)               # est_cardinal(Card(E∖X))
    card_ZERO = _est_cardinal_du_cardinal(E.VIDE)          # est_cardinal(Card∅) = est_cardinal(0)
    inner_ante = conjonction_intro(conjonction_intro(card_cD, card_ZERO), sum_eq_p0)
    cardD_eq_0 = N.modus_ponens(inner_ante, P_inst)        # Card(E∖X) = 0
    assert cardD_eq_0.conclusion == egal(cD, ZERO)

    # ── (5) E∖X = ∅ ─────────────────────────────────────────────────────────
    # ZERO = Card∅ ; cardinal_egal_zero_ssi_vide(E∖X) : (Card(E∖X)=Card∅) ⟺ (E∖X=∅)
    ssi = cardinal_egal_zero_ssi_vide(EmX)                  # ⟺
    D_vide = N.modus_ponens(cardD_eq_0, equivalence_avant(ssi))   # E∖X = ∅
    assert D_vide.conclusion == egal(EmX, E.VIDE)

    # ── (6) E = X∪(E∖X) = X∪∅ = X ⇒ X = E ───────────────────────────────────
    # X∪(E∖X) = X∪∅  via E∖X=∅ (congruence)
    reun_eq_Xv = N.modus_ponens(
        D_vide, congruence_terme(EmX, E.VIDE, E.reunion(vX, var("w")), w="w"))  # X∪(E∖X) = X∪∅
    Xv_eq_X = reunion_vide_neutre(vX)                      # X∪∅ = X
    reun_eq_X = composer_egalites(reun_eq_Xv, Xv_eq_X)     # X∪(E∖X) = X
    # E = X∪(E∖X) = X
    E_eq_X = composer_egalites(E_eq_reun_rev, reun_eq_X)   # E = X
    X_eq_E = N.modus_ponens(E_eq_X, symetrie(vE, vX))      # X = E
    assert X_eq_E.conclusion == egal(vX, vE)

    res = N.loi_deduction(ante, X_eq_E)
    assert res.conclusion == partie_egal_cardinal_egal_enonce(vX, vE), "conclusion ≠ énoncé"
    assert res.est_clos and not res.hypotheses, "partie_egal_cardinal_egal : non close !"
    return res


# ── helpers ───────────────────────────────────────────────────────────────────
def symetrie_thm(eq_thm):
    """De ⊢ a=b déduit ⊢ b=a (via symetrie + MP)."""
    a, b = eq_thm.conclusion.termes
    return N.modus_ponens(eq_thm, symetrie(a, b))


def _entier_de_fini_ensemble(fini_thm, tX):
    """De ⊢ est_fini_ensemble(X) déduit ⊢ est_entier(Card X) (mêmes formules)."""
    # est_fini_ensemble(X) = est_fini(Card X) = est_entier(Card X) par définition
    cible = est_entier(cardinal(tX))
    assert fini_thm.conclusion == cible, \
        f"est_fini_ensemble(X) ≠ est_entier(Card X) : {fini_thm.conclusion} vs {cible}"
    return fini_thm


def _est_cardinal_du_cardinal(tEns):
    """⊢ est_cardinal(Card tEns)  =  (∃X)(Card tEns = Card X)  (binder « X » aligné
    sur est_cardinal), témoin X:=tEns.  Capture-safe pour tEns τ-terme quelconque."""
    tEns = _t(tEns)
    cT = cardinal(tEns)
    corps = egal(cT, cardinal(var("X")))                  # Card tEns = Card X   (liant X)
    temoin = N.reflexivite(cT)                            # Card tEns = Card tEns
    s5 = N.s5(corps, tEns, "X")                           # (tEns|X)corps ⇒ (∃X)corps
    res = N.modus_ponens(temoin, s5)                      # est_cardinal(Card tEns)
    assert res.conclusion == est_cardinal(cT), \
        f"_est_cardinal_du_cardinal : {res.conclusion} vs {est_cardinal(cT)}"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  🎯 COROLLAIRE 2 §III.4 — une partie PROPRE d'un fini a un cardinal STRICTEMENT
#  plus petit
# ════════════════════════════════════════════════════════════════════════════
def cor2_partie_propre_inf_strict_enonce(X="Xpe", Eens="Epe"):
    """⊢-cible : ( X⊂E et ¬(X=E) et est_fini_ensemble(E) ) ⇒ Card X < Card E."""
    from bourbaki.logique.i_1_termes_relations.formule import impl, inclus, non
    vX, vE = _t(X), _t(Eens)
    ante = et(et(inclus(vX, vE), non(egal(vX, vE))), est_fini_ensemble(vE))
    return impl(ante, inf_strict_card(cardinal(vX), cardinal(vE)))


def cor2_partie_propre_inf_strict(X="Xpe", Eens="Epe"):
    """🎯 ⊢ ( X⊂E et ¬(X=E) et est_fini_ensemble(E) ) ⇒ Card X < Card E.   (CLOS, 0 hyp.)

    Cor. 2 §III.4 (pigeonhole, forme stricte).  Contraposée du sous-lemme :
      • Card X ≤ Card E (monotonie : X⊂E ⇒ X≤E ⇒ Card X≤Card E) ;
      • Card X ≠ Card E : sinon (X⊂E et fini E et Card X=Card E) ⇒ X=E
        (partie_egal_cardinal_egal), contredisant X≠E ;
      • Card X < Card E := (Card X≤Card E et Card X≠Card E)."""
    from bourbaki.logique.i_1_termes_relations.formule import impl, inclus, non
    from bourbaki.entiers.iii_4_entiers_finis.iii_4_2_finis_props.ensembles_finis_props import (
        partie_inf_egal_card, _pont_inf_egal_card,
    )
    vX, vE = _t(X), _t(Eens)
    cX, cE = cardinal(vX), cardinal(vE)
    incl = inclus(vX, vE)
    Xneq = non(egal(vX, vE))
    Efini = est_fini_ensemble(vE)

    ante = et(et(incl, Xneq), Efini)
    h = N.assume(ante)
    h_incl = conjonction_elim_gauche(conjonction_elim_gauche(h))    # X⊂E
    h_neq = conjonction_elim_droite(conjonction_elim_gauche(h))     # ¬(X=E)
    h_fini = conjonction_elim_droite(h)                            # fini E

    # Card X ≤ Card E
    le_XE = N.modus_ponens(h_incl, partie_inf_egal_card(vX, vE))    # X ≤ E
    le_card = N.modus_ponens(le_XE, _pont_inf_egal_card(vX, vE))    # Card X ≤ Card E
    assert le_card.conclusion == _inf_egal(cX, cE)

    # ¬(Card X = Card E)  par réduction à l'absurde via le sous-lemme
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import contraposition
    sublem = partie_egal_cardinal_egal(vX, vE)                     # (X⊂E et fini E et CardX=CardE)⇒X=E
    h_cardeq = N.assume(egal(cX, cE))                              # supposons Card X = Card E
    sub_ante = conjonction_intro(conjonction_intro(h_incl, h_fini), h_cardeq)
    X_eq_E = N.modus_ponens(sub_ante, sublem)                      # X = E  [X⊂E, fini E, CardX=CardE]
    impl_cardeq = N.loi_deduction(egal(cX, cE), X_eq_E)           # (CardX=CardE) ⇒ (X=E)  [X⊂E, fini E]
    contra_impl = contraposition(impl_cardeq)                     # ¬(X=E) ⇒ ¬(CardX=CardE)
    neq_card = N.modus_ponens(h_neq, contra_impl)                 # ¬(Card X = Card E)
    assert neq_card.conclusion == non(egal(cX, cE)), \
        f"neq_card : {neq_card.conclusion} vs {non(egal(cX, cE))}"

    inf_strict = conjonction_intro(le_card, neq_card)              # Card X < Card E
    assert inf_strict.conclusion == inf_strict_card(cX, cE)

    res = N.loi_deduction(ante, inf_strict)
    assert res.conclusion == cor2_partie_propre_inf_strict_enonce(vX, vE), "conclusion ≠ énoncé"
    assert res.est_clos and not res.hypotheses, "cor2 : non close !"
    return res


def _inf_egal(x, y):
    from bourbaki.cardinaux.ensembles_cardinaux import inf_egal_card
    return inf_egal_card(x, y)


__all__ = ["partie_egal_cardinal_egal", "partie_egal_cardinal_egal_enonce",
           "cor2_partie_propre_inf_strict", "cor2_partie_propre_inf_strict_enonce"]
