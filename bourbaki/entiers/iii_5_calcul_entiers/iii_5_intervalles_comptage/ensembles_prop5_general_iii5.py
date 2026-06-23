"""§III.5 — PROPOSITION 5 (forme GÉNÉRALE), E III.38.

    « Si a et b sont des entiers tels que a ≤ b, l'intervalle [a,b] est un ensemble
      fini dont le nombre d'éléments est (b − a) + 1. »

Bourbaki réduit le cas général au cas a = 0 (forme `prop5_intervalle_zero`,
Card([0,b']) = b'+1) via la PROP. 4 (E III.37) : x ↦ a+x est un isomorphisme
strictement croissant de [0,b'] sur [a, a+b'].  Avec b' := b − a et
a + (b − a) = b (Cor. 4 §III.5, `soustraction_caracterisation`), l'intervalle
[a, a+b'] = [a, b], donc

    Card([a,b]) = Card([0, b−a]) = (b−a) + 1.

ASSEMBLAGE (ce module).  Les briques sont déjà fusionnées :
  • `prop5_intervalle_zero(b')`  ⊢ est_entier(b') ⇒ Card([0,b']) = b'+1 ;
  • `_prop1_direct_t(U,V)`       ⊢ Eq(U,V) ⇒ (Card U = Card V)  (Prop. 1 §III.3) ;
  • `soustraction_caracterisation` ⊢ (card a, card b, a≤b) ⇒ a + (b−a) = b.

RÉSIDUS HONNÊTES (hypothèses, conclusion ∉ hypothèses — JAMAIS vacus/postulé) :
  • `equipotent([0, b−a], [a, b])` — l'équipotence-témoin de la Prop. 4
    (le graphe-bijection x↦a+x ; sa réification BUTE sur la capture τ des liants
    u,v,z internes au terme cardinal a⊔x — chantier graphe_terme séparé) ;
  • `est_entier(b − a)`           — la finitude du complément (b−a ≤ b finie via
    downward-closure C61 — assemblage séparé).
Tout le reste (l'épine arithmétique : a+(b−a)=b, réécriture d'intervalle,
Card par équipotence, Card[0,b']=b'+1) est INCONDITIONNEL et vérifié ici.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, et, impl
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
)
from bourbaki.logique.i_4_egalitaires.tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)

from bourbaki.cardinaux.ensembles_cardinaux import (
    est_cardinal, cardinal, inf_egal_card, equipotent,
)
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, ZERO, est_entier
from bourbaki.entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers_theoremes import fini_implique_cardinal
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_cardinale_binaire,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_2_inegalites_ordre_soustraction.ensembles_soustraction_iii5 import (
    diff_somme, soustraction_caracterisation,
)
from bourbaki.entiers.iii_5_calcul_entiers.iii_5_intervalles_comptage.ensembles_prop5_prop4_iii5 import prop5_intervalle_zero
from bourbaki.cardinaux.arithmetique.ensembles_arith_cardinale import _prop1_direct_t


def _t(t):
    return t if isinstance(t, Terme) else var(t)


# ── la différence b − a et l'intervalle source/cible ──────────────────────────
def _bprime(va, vb):
    """b − a := τc(b = a+c)  (le témoin canonique du complément, Cor. 4 §III.5)."""
    return diff_somme(vb, va)


def prop5_intervalle_general_enonce(a="ag5", b="bg5"):
    """Formule :
        ( est_entier(a) et est_entier(b) et a≤b et est_entier(b−a)
          et Eq([0,b−a],[a,b]) )
        ⇒  Card([a,b]) = (b−a) + 1.

    PROPOSITION 5 §III.5 (E III.38) forme GÉNÉRALE.  Les deux derniers conjoints
    de la prémisse (finitude de b−a, équipotence-témoin Prop. 4) sont les résidus
    honnêtes documentés en tête de module ; l'épine arithmétique est prouvée."""
    va, vb = _t(a), _t(b)
    bprime = _bprime(va, vb)
    seg_zero = E.intervalle_entiers(ZERO, bprime)        # [0, b−a]
    seg_ab = E.intervalle_entiers(va, vb)                # [a, b]
    premisse = et(et(et(et(est_entier(va), est_entier(vb)), inf_egal_card(va, vb)),
                     est_entier(bprime)),
                  equipotent(seg_zero, seg_ab))
    return impl(premisse, egal(cardinal(seg_ab), successeur(bprime)))


def prop5_intervalle_general(a="ag5", b="bg5"):
    """⊢ ( est_entier a et est_entier b et a≤b et est_entier(b−a)
            et Eq([0,b−a],[a,b]) )  ⇒  Card([a,b]) = (b−a) + 1.

    PROPOSITION 5 §III.5 (E III.38), forme GÉNÉRALE.  Assemblage :
      1. Eq([0,b−a],[a,b]) ⇒ Card([0,b−a]) = Card([a,b])   (_prop1_direct_t, Prop. 1) ;
      2. est_entier(b−a) ⇒ Card([0,b−a]) = (b−a)+1          (prop5_intervalle_zero) ;
      3. transitivité : Card([a,b]) = Card([0,b−a]) = (b−a)+1.
    (Cette forme garde les deux résidus honnêtes ; le pont a+(b−a)=b sert à
    `prop5_intervalle_general_via_complement`, où l'intervalle [a,a+(b−a)] est
    identifié à [a,b].)"""
    va, vb = _t(a), _t(b)
    bprime = _bprime(va, vb)
    seg_zero = E.intervalle_entiers(ZERO, bprime)        # [0, b−a]
    seg_ab = E.intervalle_entiers(va, vb)                # [a, b]
    succ_bp = successeur(bprime)                         # (b−a)+1

    premisse = et(et(et(et(est_entier(va), est_entier(vb)), inf_egal_card(va, vb)),
                     est_entier(bprime)),
                  equipotent(seg_zero, seg_ab))
    h = N.assume(premisse)
    h_ent_bp = conjonction_elim_droite(conjonction_elim_gauche(h))   # est_entier(b−a)
    h_eq = conjonction_elim_droite(h)                               # Eq([0,b−a],[a,b])

    # (1) Card([0,b−a]) = Card([a,b])   (Prop. 1 sens direct, version TERME)
    prop1 = _prop1_direct_t(seg_zero, seg_ab)            # Eq(·,·) ⇒ Card·=Card·
    card0_eq_cardab = N.modus_ponens(h_eq, prop1)        # Card[0,b−a] = Card[a,b]

    # (2) Card([0,b−a]) = (b−a)+1   (forme a=0, sous est_entier(b−a))
    p5z = prop5_intervalle_zero(bprime)                  # est_entier(b−a) ⇒ Card[0,b−a]=succ(b−a)
    card0_eq_succ = N.modus_ponens(h_ent_bp, p5z)        # Card[0,b−a] = (b−a)+1

    # (3) Card[a,b] = Card[0,b−a] = (b−a)+1
    cardab_eq_card0 = N.modus_ponens(card0_eq_cardab,
        symetrie(cardinal(seg_zero), cardinal(seg_ab)))  # Card[a,b] = Card[0,b−a]
    cardab_eq_succ = composer_egalites(cardab_eq_card0, card0_eq_succ)   # Card[a,b]=(b−a)+1

    res = N.loi_deduction(premisse, cardab_eq_succ)
    assert res.conclusion == prop5_intervalle_general_enonce(a, b), \
        "prop5_intervalle_general : conclusion ≠ énoncé attendu"
    return res


# ── BRIQUE INCONDITIONNELLE (épine) : a + (b − a) = b ─────────────────────────
def somme_diff_egale_grand(a="ag5", b="bg5"):
    """⊢ ( est_entier a et est_entier b et a≤b ) ⇒ ( a + (b−a) = b ).  (Cor. 4 §III.5.)

    Décharge `est_cardinal` (de est_entier via fini_implique_cardinal) puis
    `soustraction_caracterisation`.  INCONDITIONNEL.  Sert à identifier
    l'intervalle-cible [a, a+(b−a)] à [a,b]."""
    va, vb = _t(a), _t(b)
    ante = et(et(est_entier(va), est_entier(vb)), inf_egal_card(va, vb))
    h = N.assume(ante)
    h_enta = conjonction_elim_gauche(conjonction_elim_gauche(h))
    h_entb = conjonction_elim_droite(conjonction_elim_gauche(h))
    h_le = conjonction_elim_droite(h)
    card_a = N.modus_ponens(h_enta, fini_implique_cardinal(va))      # est_cardinal a
    card_b = N.modus_ponens(h_entb, fini_implique_cardinal(vb))      # est_cardinal b
    sc = soustraction_caracterisation(a, b)        # (card a, card b, a≤b) ⇒ a+(b−a)=b
    eq = N.modus_ponens(conjonction_intro(conjonction_intro(card_a, card_b), h_le), sc)
    return N.loi_deduction(ante, eq)               # ⇒ a+(b−a)=b


__all__ = [
    "prop5_intervalle_general", "prop5_intervalle_general_enonce",
    "somme_diff_egale_grand",
]
