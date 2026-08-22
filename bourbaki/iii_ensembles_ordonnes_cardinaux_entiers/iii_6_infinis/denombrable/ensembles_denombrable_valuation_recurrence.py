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


__all__ = ["exposant_zero_un", "ops_produit_un_droite"]
