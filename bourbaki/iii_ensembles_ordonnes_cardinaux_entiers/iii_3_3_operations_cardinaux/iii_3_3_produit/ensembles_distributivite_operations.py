# -*- coding: utf-8 -*-
"""§III.3.3 Prop.5 c) — DISTRIBUTIVITÉ AU NIVEAU DES OPÉRATIONS cardinales.

⊢ a·(b+c) = a·b + a·c   sur les opérations RÉELLES du dépôt :
    Card(A × Card(B⊔C)) = Card(Card(A×B) ⊔ Card(A×C))
  (produit_cardinal_binaire / somme_cardinale_binaire).

BRIQUE DÉSIGNÉE PAR LA MACHINE (21 août 2026, EXP6 du marcheur, MESURES §6 de
A4) : pointé sur ce but avec le théorème niveau-ENSEMBLES au pool, le marcheur
a certifié ce qu'il pouvait, réfuté les schémas faux, et rendu « non-certifié »
sur les quatre morphismes — le chaînon manquant est LE PONT DU RESPECT DE
L'ÉQUIPOTENCE : les opérations cardinales prennent le Card de leurs arguments,
le théorème ensembliste travaille sur les ensembles nus.

Assemblage en trois égalités composées (aucun nouvel axiome, tout est déjà
clos) :
  1. Eq(a,a) ∧ Eq(Card(B⊔C), B⊔C)  ⇒[eq_produit_invariant]
       Eq(a × Card(B⊔C), a × (B⊔C))     ⇒[Prop.1]  Card = Card ;
  2. distributivite_cardinale : Card(a×(B⊔C)) = Card((a×b)⊔(a×c)) ;
  3. Eq(a×b, Card(a×b)) ∧ Eq(a×c, Card(a×c))  ⇒[eq_somme_invariant]
       Eq((a×b)⊔(a×c), Card(a×b)⊔Card(a×c))  ⇒[Prop.1]  Card = Card ;
  puis composer_egalites × 2.

Les lemmes à noms (`equipotent_son_cardinal`, la symétrie d'Eq) sont
∀-clôturés puis instanciés AU TERME — jamais var() sur un Terme (piège mesuré
le 21 août sur l'énoncé du Th.1 de la division : var(Terme) fabrique un objet
difforme).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, instancie)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    composer_egalites)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    somme_disjointe, somme_cardinale_binaire)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import (
    produit_cardinal_binaire, _prop1_direct_t)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_distributivite_cardinale import (
    distributivite_cardinale)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_equipotence import (
    eq_produit_invariant)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (
    eq_somme_invariant)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.equipotence.ensembles_equipotence import (
    equipotence_reflexive)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_theoremes import (
    equipotent_son_cardinal, _sym_all)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _eq_refl_t(t):
    """⊢ Eq(t, t) pour un TERME (∀-clôture du lemme à nom, puis instance)."""
    return instancie(N.generalisation("X", equipotence_reflexive("X")), t)


def _eq_card_t(t):
    """⊢ Eq(t, Card t) pour un TERME."""
    return instancie(N.generalisation("X", equipotent_son_cardinal("X")), t)


def _eq_sym_t(thm, u, v):
    """⊢ Eq(u,v) ⟹ ⊢ Eq(v,u) (symétrie ∀-clôturée instanciée aux termes)."""
    return N.modus_ponens(thm, instancie(instancie(_sym_all(), u), v))


def enonce_distributivite_operations(a="A", b="B", c="C"):
    va, vb, vc = _t(a), _t(b), _t(c)
    return egal(produit_cardinal_binaire(va, somme_cardinale_binaire(vb, vc)),
                somme_cardinale_binaire(produit_cardinal_binaire(va, vb),
                                        produit_cardinal_binaire(va, vc)))


# (Prop. 5 c) au niveau des OPÉRATIONS — corollaire-pont du cas ensembliste.)
# @livre Ch.III §3.3 Prop.5 | E III.26 L.20-23 | PDF p.129
# @livre Ch.III §3.3 Cor.- | E III.27 L.13-13 | PDF p.130
def distributivite_operations(a="A", b="B", c="C"):
    """🎯 ⊢ a·(b+c) = a·b + a·c  au niveau des opérations cardinales, CLOS."""
    va, vb, vc = _t(a), _t(b), _t(c)
    BuC = somme_disjointe(vb, vc)                       # B⊔C (ensembles)
    SCbc = somme_cardinale_binaire(vb, vc)              # b+c = Card(B⊔C)
    AxB, AxC = E.produit(va, vb), E.produit(va, vc)     # A×B, A×C
    Pab = produit_cardinal_binaire(va, vb)              # a·b = Card(A×B)
    Pac = produit_cardinal_binaire(va, vc)              # a·c = Card(A×C)

    #   1. Card(a × (b+c)) = Card(a × (B⊔C))
    eq_refl = _eq_refl_t(va)                            # Eq(a, a)
    eq_card = _eq_card_t(BuC)                           # Eq(B⊔C, Card(B⊔C))
    eq_cs = _eq_sym_t(eq_card, BuC, SCbc)               # Eq(b+c, B⊔C)
    inv1 = eq_produit_invariant("F", "G", va, SCbc, va, BuC)
    eq1 = N.modus_ponens(conjonction_intro(eq_refl, eq_cs), inv1)
    g1 = N.modus_ponens(eq1, _prop1_direct_t(E.produit(va, SCbc),
                                             E.produit(va, BuC)))

    #   2. Card(a × (B⊔C)) = Card((A×B) ⊔ (A×C))   (le théorème ensembliste)
    g2 = distributivite_cardinale(va, vb, vc)

    #   3. Card((A×B) ⊔ (A×C)) = Card(a·b ⊔ a·c)
    eq3 = N.modus_ponens(
        conjonction_intro(_eq_card_t(AxB), _eq_card_t(AxC)),
        eq_somme_invariant("F", "G", AxB, AxC, Pab, Pac))
    g3 = N.modus_ponens(eq3, _prop1_direct_t(somme_disjointe(AxB, AxC),
                                             somme_disjointe(Pab, Pac)))

    res = composer_egalites(composer_egalites(g1, g2), g3)
    assert res.est_clos, "distributivite_operations : hypothèses résiduelles"
    assert res.conclusion == enonce_distributivite_operations(a, b, c), \
        "distributivite_operations : conclusion inattendue"
    return res


__all__ = ["enonce_distributivite_operations", "distributivite_operations"]
