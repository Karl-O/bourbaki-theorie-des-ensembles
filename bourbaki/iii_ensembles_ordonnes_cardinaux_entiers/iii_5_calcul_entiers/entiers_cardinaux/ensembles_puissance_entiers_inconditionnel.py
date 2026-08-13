"""§III.5.1 — Corollaire 3 INCONDITIONNEL : la PUISSANCE de deux entiers est un
entier, SANS aucune hypothèse de support.

        🎯  ⊢  ( Fini a et Fini b )  ⇒  Fini( a^b ).

`ensembles_n_arith_iii5.puissance_entiers_ferme` prouve cet énoncé SOUS deux
hypothèses de support (B0) et (B) (« exponent-invariance ») :

    (B0)  Card(𝓕(0;a)) = Card(𝓕(∅;a))           [0 = ZERO = Card(∅)]
    (B)   (∀n) Card(𝓕(n+1;a)) = Card(𝓕(n⊔{∅};a)) [n+1 = successeur n = Card(n⊔{∅})]

Ces deux hypothèses sont des INSTANCES du keystone `eq_exposant_invariant`
(`ensembles_eq_exposant_invariant`, CLOS) :

        Eq(X, Y)  ⇒  Eq(𝓕(X;a), 𝓕(Y;a)),

composé à `_prop1_direct_t` (Eq ⇒ égalité des cardinaux) :

        Eq(X, Y)  ⇒  Card(𝓕(X;a)) = Card(𝓕(Y;a)).

Le « pont »  Eq(Card S, S)  (tout ensemble est équipotent à son cardinal,
`equipotent_son_cardinal` + symétrie `equipotence_symetrique`) fournit, en S=∅
(resp. S=n⊔{∅}, où Card(n⊔{∅})=successeur n), l'équipotence Eq(ZERO,∅) (resp.
Eq(successeur n, n⊔{∅})) qui DÉCHARGE (B0) (resp. (B)).  On décharge alors les
deux antécédents de `puissance_entiers_ferme` et on obtient l'énoncé PROPRE,
SANS (B0)/(B), CERTIFIÉ INCONDITIONNELLEMENT.  theorie_ensembles INCHANGÉE (22).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, pourtout, impl, et
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import equipotent_son_cardinal
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_bijection import equipotence_symetrique
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.somme_produit_bornes.ensembles_eq_exposant_invariant import eq_exposant_invariant
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import _prop1_direct_t
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_5_exposant.definition.ensembles_exposant_cardinal import (
    exposant_cardinal_binaire,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import somme_disjointe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import successeur, ZERO, est_fini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.entiers_cardinaux.ensembles_n_arith_iii5 import (
    exposant_invariance_enonce, exposant_invariance_zero_enonce,
    puissance_entiers_ferme,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── le pont  Eq(Card S, S)  pour un TERME S  (capture-safe) ───────────────────
def _eq_card_set(S):
    """⊢ Eq(Card S, S)   (Card S est équipotent à S — tout ensemble l'est à son cardinal).

    equipotent_son_cardinal ⊢ Eq(S, Card S) ; equipotence_symetrique le renverse.
    Le binder-témoin de l'∃ doit être « F » (défaut de equipotent_son_cardinal)
    pour que la mineure s'apparie à l'antécédent de equipotence_symetrique."""
    vS = _t(S)
    g = N.generalisation("Xb", equipotent_son_cardinal("Xb"))
    eq_s_cards = instancie(g, vS)                                 # Eq(S, Card S)
    sym = equipotence_symetrique("F", "Xs", "Ys")                # Eq(Xs,Ys) ⇒ Eq(Ys,Xs)
    symg = N.generalisation("Xs", N.generalisation("Ys", sym))
    sym_i = instancie(instancie(symg, vS), cardinal(vS))         # Eq(S,Card S) ⇒ Eq(Card S,S)
    return N.modus_ponens(eq_s_cards, sym_i)                     # Eq(Card S, S)


# ── eq_exposant_invariant en version TERME (généralise sur les défauts X,Y,a) ──
_EQI = N.generalisation("X", N.generalisation("Y",
        N.generalisation("a", eq_exposant_invariant())))


def _eq_exposant_invariant_t(X, Y, a):
    """⊢ Eq(X,Y) ⇒ Eq(𝓕(X;a), 𝓕(Y;a))   (le keystone, instancié aux TERMES X,Y,a)."""
    return instancie(instancie(instancie(_EQI, _t(X)), _t(Y)), _t(a))


def _card_applications_egal(eqsets, X, Y, a):
    """{eqsets ⊢ Eq(X,Y)} ⊢ Card(𝓕(X;a)) = Card(𝓕(Y;a)).

    keystone (Eq(X,Y) ⇒ Eq(𝓕(X;a),𝓕(Y;a))) puis _prop1_direct_t (Eq ⇒ Card=Card)."""
    eqf = N.modus_ponens(eqsets, _eq_exposant_invariant_t(X, Y, a))   # Eq(𝓕(X;a),𝓕(Y;a))
    p1 = _prop1_direct_t(E.applications(_t(X), _t(a)), E.applications(_t(Y), _t(a)))
    return N.modus_ponens(eqf, p1)                                   # Card(𝓕(X;a))=Card(𝓕(Y;a))


# ══════════════════════════════════════════════════════════════════════════════
#  (B0) et (B) : LES DEUX PONTS DÉCHARGÉS via le keystone
# ══════════════════════════════════════════════════════════════════════════════
def B0_preuve(a="apuf"):
    """⊢ exposant_invariance_zero_enonce(a)  =  Card(𝓕(0;a)) = Card(𝓕(∅;a)).

    0 = ZERO = Card(∅) ; Eq(ZERO,∅) = Eq(Card ∅, ∅) (_eq_card_set en S=∅) ; le
    keystone en X=ZERO, Y=∅ donne l'égalité des cardinaux."""
    va = _t(a)
    b0 = _card_applications_egal(_eq_card_set(E.VIDE), ZERO, E.VIDE, va)
    assert b0.conclusion == exposant_invariance_zero_enonce(va), \
        "B0_preuve : conclusion ≠ exposant_invariance_zero_enonce"
    assert b0.est_clos, "B0_preuve : non clos"
    return b0


def B_preuve(a="apuf", n="npuf"):
    """⊢ exposant_invariance_enonce(a,n)  =  Card(𝓕(n+1;a)) = Card(𝓕(n⊔{∅};a)).

    n+1 = successeur n = Card(n⊔{∅}) ; Eq(successeur n, n⊔{∅}) = Eq(Card(n⊔{∅}),
    n⊔{∅}) (_eq_card_set en S=n⊔{∅}) ; keystone en X=successeur n, Y=n⊔{∅}."""
    va, vn = _t(a), _t(n)
    n_sing = somme_disjointe(vn, E.singleton(E.VIDE))            # n⊔{∅}
    bn = _card_applications_egal(_eq_card_set(n_sing), successeur(vn), n_sing, va)
    assert bn.conclusion == exposant_invariance_enonce(va, vn), \
        "B_preuve : conclusion ≠ exposant_invariance_enonce"
    assert bn.est_clos, "B_preuve : non clos"
    return bn


# ══════════════════════════════════════════════════════════════════════════════
#  🎯  L'ÉNONCÉ PROPRE INCONDITIONNEL
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.III §5.1 Cor.3 | E III.36 L.9-11 | PDF p.139
def puissance_entiers_ferme_inconditionnel(a="apuf", b="bpuf"):
    """🎯 ⊢ ( Fini a et Fini b ) ⇒ Fini( a^b ).   (Cor. 3 §III.5.1, INCONDITIONNEL.)

    Décharge des deux antécédents (B0) et (B) de `puissance_entiers_ferme` par
    `B0_preuve` / `B_preuve` (instances du keystone `eq_exposant_invariant`).
    Conclusion = l'énoncé PROPRE, SANS (B0)/(B).  est_clos=True, theorie=22."""
    va, vb = _t(a), _t(b)
    pef = puissance_entiers_ferme()              # B0 ⇒ (Buniv ⇒ (Fini a et Fini b ⇒ Fini a^b))
    b0 = B0_preuve(va)                           # B0
    # Buniv := (∀mPpu) exposant_invariance_enonce(a, mPpu)  — généraliser B_preuve(a, mPpu)
    Buniv = N.generalisation("mPpu", B_preuve(va, var("mPpu")))
    assert Buniv.conclusion == pourtout("mPpu", exposant_invariance_enonce(va, "mPpu")), \
        "Buniv : forme ≠ (∀m)exposant_invariance_enonce attendu par puissance_entiers_ferme"
    step1 = N.modus_ponens(b0, pef)              # Buniv ⇒ (Fini a et Fini b ⇒ Fini a^b)
    final = N.modus_ponens(Buniv, step1)         # Fini a et Fini b ⇒ Fini a^b
    cible = impl(et(est_fini(va), est_fini(vb)),
                 est_fini(exposant_cardinal_binaire(va, vb)))
    assert final.conclusion == cible, \
        "puissance_entiers_ferme_inconditionnel : conclusion ≠ cible PROPRE"
    return final


__all__ = ["B0_preuve", "B_preuve", "puissance_entiers_ferme_inconditionnel"]
