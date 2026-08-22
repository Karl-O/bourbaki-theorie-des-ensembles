# -*- coding: utf-8 -*-
"""§III.6.3 — D1a : L'ENSEMBLE MARQUÉ E⊔{∅} A LE MÊME CARDINAL QUE E (E infini).

🎯 CIBLES (W := E ⊔ {∅} = (E×{0}) ∪ ({∅}×{1}), la somme disjointe concrète) :

    carte_w_egale : { est_infini(Card E) }  ⊢  Card(W) = Card(E)
    eq_w_e        : { est_infini(Card E) }  ⊢  Eq(W, E)

La chaîne Dedekind au niveau des cardinaux :
    Card(W) = Card E + Card {∅}          [somme_disjointe_cardinal, réflexivités]
            = Card(Card E ⊔ {∅})          [même lemme sur (Card E, {∅}) ;
                                           Card(Card E)=Card E par idempotence]
            = successeur(Card E)          [DÉFINITIONNEL : succ a = Card(a⊔{∅})]
            = Card E                      [dedekind_cardinal sous est_infini ;
                                           est_cardinal(Card E) par S5 trivial]
puis la Proposition 1 (sens réciproque) transforme l'égalité des cardinaux en
équipotence : Eq(W, E) — le témoin bijectif h : W → E de l'étape D1b.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal, est_cardinal, equipotent,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    equipotent_son_cardinal, equipotent_si_cardinal_egal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_arith_somme import (
    somme_disjointe_cardinal, _prop1_direct_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis import (
    est_infini,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.ensembles_infinis_props import (
    dedekind_cardinal,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


SINGZ = E.singleton(E.VIDE)                                 # {∅} (le marqueur-côté)


def ensemble_marque(e):
    """W := E ⊔ {∅} = (E×{∅}) ∪ ({∅}×{{∅}})  (la somme disjointe concrète)."""
    return somme_disjointe(_t(e), SINGZ)


def card_idempotent_terme(t):
    """⊢ Card(Card T) = Card T   (idempotence : Eq(T, Card T) + Prop. 1 direct)."""
    vt = _t(t)
    eq = instancie(N.generalisation("X", equipotent_son_cardinal("X")), vt)
    direct = N.modus_ponens(eq, _prop1_direct_t(vt, cardinal(vt)))
    return N.modus_ponens(direct, symetrie(cardinal(vt), cardinal(cardinal(vt))))


def est_cardinal_du_cardinal(t, x="X"):
    """⊢ est_cardinal(Card T)   (témoin X := T, S5 sur la réflexivité)."""
    vt = _t(t)
    R = egal(cardinal(vt), cardinal(var(x)))
    return N.modus_ponens(N.reflexivite(cardinal(vt)), N.s5(R, vt, x))


def carte_w_egale(e="Eld"):
    """🎯 D1a : { est_infini(Card E) } ⊢ Card(E⊔{∅}) = Card E   [1 hyp]."""
    ve = _t(e)
    cE = cardinal(ve)
    W = ensemble_marque(ve)
    # Card(W) = Card E + Card {∅}   (bien-définition, prémisses réflexives)
    app1 = N.modus_ponens(
        conjonction_intro(N.reflexivite(cE), N.reflexivite(cardinal(SINGZ))),
        somme_disjointe_cardinal(ve, SINGZ, cE, cardinal(SINGZ)))
    # Card(Card E ⊔ {∅}) = Card E + Card {∅}   (même lemme sur (Card E, {∅}))
    app2 = N.modus_ponens(
        conjonction_intro(card_idempotent_terme(ve),
                          N.reflexivite(cardinal(SINGZ))),
        somme_disjointe_cardinal(cE, SINGZ, cE, cardinal(SINGZ)))
    #   Card(W) = Card E + Card {∅} = Card(Card E ⊔ {∅}) = succ(Card E)  [déf.]
    succ_cE = cardinal(somme_disjointe(cE, SINGZ))          # = successeur(Card E)
    somme_c = cardinal(somme_disjointe(cE, cardinal(SINGZ)))  # = Card E + Card {∅}
    vers_succ = composer_egalites(app1, N.modus_ponens(
        app2, symetrie(succ_cE, somme_c)))
    # dedekind : sous est_infini(Card E), successeur(Card E) = Card E
    ded = N.modus_ponens(est_cardinal_du_cardinal(ve),
                         instancie(N.generalisation("a", dedekind_cardinal("a")),
                                   cE))                     # infini ⇔ cE=succ cE
    h_inf = N.assume(est_infini(cE))                        # [HONNÊTE]
    eq_succ = N.modus_ponens(h_inf, equivalence_avant(ded))  # cE = succ(cE)
    succ_eq = N.modus_ponens(eq_succ, symetrie(cE, succ_cE))  # succ(cE) = cE
    res = composer_egalites(vers_succ, succ_eq)             # Card(W) = Card E
    assert res.conclusion == egal(cardinal(W), cE), "carte_w_egale : forme"
    assert list(res.hypotheses) == [est_infini(cE)], "carte_w_egale : hyps"
    return res


def eq_w_e(e="Eld"):
    """🎯 D1a : { est_infini(Card E) } ⊢ Eq(E⊔{∅}, E)   [1 hyp — Prop. 1 réciproque]."""
    ve = _t(e)
    W = ensemble_marque(ve)
    recip = instancie(instancie(N.generalisation("X", N.generalisation(
        "Y", equipotent_si_cardinal_egal("X", "Y"))), W), ve)
    res = N.modus_ponens(carte_w_egale(e), recip)
    assert res.conclusion == equipotent(W, ve), "eq_w_e : forme"
    assert list(res.hypotheses) == [est_infini(cardinal(ve))], "eq_w_e : hyps"
    return res


__all__ = ["SINGZ", "ensemble_marque", "card_idempotent_terme",
           "est_cardinal_du_cardinal", "carte_w_egale", "eq_w_e"]
