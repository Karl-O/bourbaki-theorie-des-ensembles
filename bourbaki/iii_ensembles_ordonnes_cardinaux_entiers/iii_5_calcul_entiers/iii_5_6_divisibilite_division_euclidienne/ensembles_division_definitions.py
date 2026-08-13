"""§III.5.6 Déf. 1 — reste, quotient, multiple, divisible, diviseur (E III.39).

DÉFINITIONS FIDÈLES (sur l'arithmétique cardinale RÉELLE : produit_cardinal_binaire,
somme_cardinale_binaire), cohérentes avec division_existence (le témoin (q,r) du
Théorème 1).  Elles SUPPLANTENT, pour la fidélité, les placeholders OPAQUES de
ensembles_entiers.divise/reste_division/quotient_division (qui codaient b·q par
app("prod_ent") faute d'arithmétique cardinale disponible à l'époque).

Bourbaki, Déf. 1 (E III.39 L.20-23) : « … le reste r et le quotient q de la division
de a par b … Si r = 0, on dit que a est multiple de b, ou que b divise a, ou que b est
un diviseur de a. »

Ce sont des CONSTRUCTEURS de termes/formules (nommage), pas des théorèmes.  Le reste et
le quotient sont les τ canoniques associés à la relation prouvée existante _R_rel.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, egal, et, existe, tau, Terme)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux import inf_strict_card
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_4_entiers_finis.iii_4_1_definitions_premiers_entiers.ensembles_entiers import est_fini
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_arith_cardinale import produit_cardinal_binaire
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_5_calcul_entiers.iii_5_6_divisibilite_division_euclidienne.ensembles_division_existence import _bqr


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# @livre Ch.III §5.6 Def.1 | E III.39 L.20-23 | PDF p.142   (b divise a)
def divise_cardinal(b, a, q="qd"):
    """« b divise a » (b | a) := (∃q)( Fini q  et  a = b·q ).   (Déf. 1, produit cardinal RÉEL.)"""
    vb, va = _t(b), _t(a)
    return existe(q, et(est_fini(var(q)), egal(va, produit_cardinal_binaire(vb, var(q)))))


# @livre Ch.III §5.6 Def.1 | E III.39 L.20-23 | PDF p.142   (a multiple de b)
def est_multiple_cardinal(a, b):
    """« a est multiple de b » := b divise a.   (Déf. 1, synonyme verbatim.)"""
    return divise_cardinal(b, a)


# @livre Ch.III §5.6 Def.1 | E III.39 L.20-23 | PDF p.142   (b diviseur de a)
def est_diviseur_cardinal(b, a):
    """« b est un diviseur de a » := b divise a.   (Déf. 1, formulation duale.)"""
    return divise_cardinal(b, a)


# @livre Ch.III §5.6 Def.1 | E III.39 L.20-23 | PDF p.142   (reste r de a par b)
def reste_cardinal(a, b, r="rr", q="qd"):
    """reste de la division de a par b := τr( (∃q)( b·q + r = a  et  r < b ) ).

    Le τ canonique du reste, aligné sur _R_rel (relation prouvée existante par
    division_existence).  Sous l'existence (b≠0, a fini), le τ-axiome le réalise."""
    va, vb = _t(a), _t(b)
    corps = existe(q, et(egal(_bqr(vb, var(q), var(r)), va), inf_strict_card(var(r), vb)))
    return tau(r, corps)


# @livre Ch.III §5.6 Def.1 | E III.39 L.20-23 | PDF p.142   (quotient q de a par b)
def quotient_cardinal(a, b, q="qd", r="rr"):
    """quotient de la division de a par b := τq( (∃r)( b·q + r = a  et  r < b ) ).   (Déf. 1, noté a/b.)"""
    va, vb = _t(a), _t(b)
    corps = existe(r, et(egal(_bqr(vb, var(q), var(r)), va), inf_strict_card(var(r), vb)))
    return tau(q, corps)


__all__ = ["divise_cardinal", "est_multiple_cardinal", "est_diviseur_cardinal",
           "reste_cardinal", "quotient_cardinal"]
