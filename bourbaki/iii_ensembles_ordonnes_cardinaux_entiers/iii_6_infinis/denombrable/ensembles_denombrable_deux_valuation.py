# -*- coding: utf-8 -*-
"""§III.6 (prérequis Lemme 2, ℵ₀·ℵ₀=ℵ₀) — la 2-VALUATION (brique W3) :
l'écriture 2^m·u (u impair) d'un entier est UNIQUE.

🎯 CIBLE FINALE (deux_valuation_unique) :
    ⊢ (Fini m,m',u,u' ∧ impair u,u' ∧ 2^m·u = 2^m'·u') ⇒ (m = m' ∧ u = u').

CE MODULE (étage 1) : les DEUX PONTS commutatif/associatif au niveau des
OPÉRATIONS cardinales (produit_cardinal_binaire), par Eq-invariance — les
versions ensemblistes (eq_produit_commute, produit_cardinal_associatif) sont
CLOSES ; on intercale les Card par eq_produit_invariant (patron
distributivite_operations) :
  • ops_produit_commutatif(a,b)  ⊢ a·b = b·a ;
  • ops_produit_associatif(a,b,c) ⊢ (a·b)·c = a·(b·c).
Étage 2 (deux_valuation_borne) : sous les hypothèses, ¬(m < m') — l'écart
d = m'−m (soustraction Cor.4), d = succ k (prédécesseur), 2^m' = 2^m·2^(succ k)
(exposant_somme_pont), simplification par 2^m (W2 + W3b) ⇒ u pair, contredit
impair u.  Étage 3 (deux_valuation_unique) : trichotomie + simplification.

theorie_ensembles INCHANGÉE (22).  Noyau INTACT.  Aucun axiome nouveau.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    instancie, conjonction_intro,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import (
    cardinal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    equipotent_son_cardinal, _sym_all,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
    equipotence_reflexive,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, _prop1_direct_t, produit_cardinal_associatif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import (
    eq_produit_commute,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import (
    eq_produit_invariant,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _eq_refl_t(t):
    """⊢ Eq(t, t) pour un TERME."""
    return instancie(N.generalisation("X", equipotence_reflexive("X")), _t(t))


def _eq_card_t(t):
    """⊢ Eq(t, Card t) pour un TERME."""
    return instancie(N.generalisation("X", equipotent_son_cardinal("X")), _t(t))


def _eq_sym_t(thm, u, v):
    """⊢ Eq(u,v) ⟹ ⊢ Eq(v,u) (symétrie ∀-clôturée instanciée aux termes)."""
    return N.modus_ponens(thm, instancie(instancie(_sym_all(), u), v))


# ══════════════════════════════════════════════════════════════════════════════
#  (1) commutativité au niveau des opérations :  a·b = b·a
# ══════════════════════════════════════════════════════════════════════════════
def ops_produit_commutatif(a, b):
    """⊢ a·b = b·a.   (eq_produit_commute ∀-clos aux termes + Prop. 1.)"""
    va, vb = _t(a), _t(b)
    g = N.generalisation("X", N.generalisation("Y", eq_produit_commute("X", "Y")))
    eqc = instancie(instancie(g, va), vb)               # Eq(a×b, b×a)
    res = N.modus_ponens(eqc, _prop1_direct_t(E.produit(va, vb), E.produit(vb, va)))
    assert res.conclusion == egal(produit_cardinal_binaire(va, vb),
                                  produit_cardinal_binaire(vb, va))
    return res


# ══════════════════════════════════════════════════════════════════════════════
#  (2) associativité au niveau des opérations :  (a·b)·c = a·(b·c)
# ══════════════════════════════════════════════════════════════════════════════
def ops_produit_associatif(a, b, c):
    """⊢ (a·b)·c = a·(b·c).   (associatif ensembliste + ponts Card intercalés.)

    (a·b)·c = Card(Card(a×b) × c) ; les trois maillons :
      g1  Card(Card(a×b) × c) = Card((a×b) × c)   [Eq(Card(a×b), a×b) + inv] ;
      g2  Card((a×b) × c) = Card(a × (b×c))       [produit_cardinal_associatif] ;
      g3  Card(a × (b×c)) = Card(a × Card(b×c))   [Eq(b×c, Card(b×c)) + inv]."""
    va, vb, vc = _t(a), _t(b), _t(c)
    AB, BC = E.produit(va, vb), E.produit(vb, vc)
    cAB, cBC = cardinal(AB), cardinal(BC)               # a·b, b·c

    eq1 = N.modus_ponens(
        conjonction_intro(_eq_sym_t(_eq_card_t(AB), AB, cAB), _eq_refl_t(vc)),
        eq_produit_invariant("F", "G", cAB, vc, AB, vc))     # Eq(Card(a×b)×c, (a×b)×c)
    g1 = N.modus_ponens(eq1, _prop1_direct_t(E.produit(cAB, vc), E.produit(AB, vc)))

    #   noms FRAIS (« Z » est le lieur τ interne de cardinal : généraliser sur
    #   « Z » déclencherait l'α-renommage @0 du τ — 7e leçon de capture)
    g_ass = N.generalisation("Xopa", N.generalisation("Yopa", N.generalisation(
        "Zopa", produit_cardinal_associatif("Xopa", "Yopa", "Zopa"))))
    g2 = instancie(instancie(instancie(g_ass, va), vb), vc)  # Card((a×b)×c)=Card(a×(b×c))

    eq3 = N.modus_ponens(
        conjonction_intro(_eq_refl_t(va), _eq_card_t(BC)),
        eq_produit_invariant("F", "G", va, BC, va, cBC))     # Eq(a×(b×c), a×Card(b×c))
    g3 = N.modus_ponens(eq3, _prop1_direct_t(E.produit(va, BC), E.produit(va, cBC)))

    res = composer_egalites(composer_egalites(g1, g2), g3)
    assert res.conclusion == egal(
        produit_cardinal_binaire(produit_cardinal_binaire(va, vb), vc),
        produit_cardinal_binaire(va, produit_cardinal_binaire(vb, vc)))
    assert not res.hypotheses, "ops_produit_associatif : hypothèses résiduelles"
    return res


__all__ = ["ops_produit_commutatif", "ops_produit_associatif"]
