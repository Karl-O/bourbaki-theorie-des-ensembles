"""§II.6.2 — Critère C55 : caractérisation de la projection canonique.

Module NEUF (pur RECOLLAGE LOGIQUE).  On NE MODIFIE AUCUN fichier existant ;
on RECOLLE deux lemmes DÉJÀ CLOS (modulo hypothèses) de
`ii_6_equivalence.ensembles_quotient_props_graphe` :

  • `projection_valeur_classe(g,e,a,b)`  {p(a)=Cl_R(a), p(b)=Cl_R(b)}
        ⊢ ( p(a)=p(b) ) ⇔ ( Cl_R(a)=Cl_R(b) )        [valeur de l'appli canonique]
  • `relation_ssi_classe_egale(g,a,b,e,x,z)`  {R réflexive dans E, R sym, R trans, b∈E}
        ⊢ R{a,b} ⇔ ( Cl_R(a)=Cl_R(b) )                [caractérisation, E.II.6.2]

CRITÈRE C55 (socle de la décomposition canonique) — sous l'union des hypothèses
des deux maillons :

  {R réflexive dans E, R sym, R trans, b∈E, p(a)=Cl_R(a), p(b)=Cl_R(b)}
        ⊢ ( p(a)=p(b) ) ⇔ ( R{a,b} ).

Stratégie (transitivité d'équivalences, « milieu » Cl_R(a)=Cl_R(b)) :
  A ⇔ B   :  eqv_p = projection_valeur_classe   [A = p(a)=p(b),  B = Cl(a)=Cl(b)] ;
  C ⇔ B   :  eqv_R = relation_ssi_classe_egale   [C = R{a,b},     B = Cl(a)=Cl(b)] ;
  B ⇔ C   :  equivalence_symetrie(eqv_R) ;
  A ⇔ C   :  equivalence_transitivite(eqv_p, B⇔C)  =  ( p(a)=p(b) ) ⇔ ( R{a,b} ).

Le « milieu » Cl_R(a)=Cl_R(b) est LITTÉRALEMENT identique dans les deux maillons
(même graphe g, mêmes points a,b → `E.classe(g,a)`, `E.classe(g,b)`), donc la
transitivité s'applique sans réécriture.

theorie_ensembles() RESTE à 22 axiomes (AUCUN axiome neuf : pur recollage logique).
Toutes les preuves sortent du noyau abrégé (primitives N.* uniquement, via les deux
maillons et les tactiques d'équivalence).  Les six hypothèses du séquent final sont
exactement l'union des hypothèses des deux maillons — rien postulé, aucune tautologie
(conclusion ∉ hypothèses), aucun affaibli.

Liants : « a »,« b » (points) ; « x » (liant de la réflexivité) ; « z » (liant
interne de relation_implique_classe_egale).  g : graphe ; e : ensemble support E.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import Terme, var, egal, equiv, appartient
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    equivalence_symetrie, equivalence_transitivite)
from bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_props_graphe import (
    projection_valeur_classe, relation_ssi_classe_egale)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ═════════════════════════════════════════════════════════════════════════════
# Critère C55 — ( p(a)=p(b) ) ⇔ ( R{a,b} )
# ═════════════════════════════════════════════════════════════════════════════
def cible_projection_c55(g="G", e="E", a="a", b="b"):
    """Cible Bourbaki du critère C55 : ( p(a)=p(b) ) ⇔ ( R{a,b} ).

    p = application_canonique(g,e), p(x)=valeur(p,x) ; R = rel_graphe(g).
    Renvoie la FORMULE attendue (pour comparer à la conclusion du théorème)."""
    vg, ve = _t(g), _t(e)
    va, vb = _t(a), _t(b)
    R = E.rel_graphe(vg)
    p = E.application_canonique(vg, ve)
    pa, pb = E.valeur(p, va), E.valeur(p, vb)
    return equiv(egal(pa, pb), R(va, vb))


# @livre Ch.II §6.2 Crit.C55 | E II.41 L.34-36 | PDF p.92
def projection_c55(g="G", e="E", a="a", b="b", x="x", z="z"):
    """{R réflexive dans E, R sym, R trans, b∈E, p(a)=Cl_R(a), p(b)=Cl_R(b)}
       ⊢ ( p(a)=p(b) ) ⇔ ( R{a,b} )   (E.II.6.2, critère C55 ; clos mod. hyp.).

    Caractérisation de la projection canonique p : E→E/R — « deux points ont même
    image par p si et seulement s'ils sont en relation ».  Socle de la décomposition
    canonique.  PUR RECOLLAGE LOGIQUE des deux maillons déjà clos :
      eqv_p : ( p(a)=p(b) ) ⇔ ( Cl_R(a)=Cl_R(b) )   (projection_valeur_classe) ;
      eqv_R : R{a,b} ⇔ ( Cl_R(a)=Cl_R(b) )           (relation_ssi_classe_egale).
    On retourne eqv_R (equivalence_symetrie) en ( Cl_R(a)=Cl_R(b) ) ⇔ R{a,b}, puis on
    transitive avec eqv_p sur le milieu commun Cl_R(a)=Cl_R(b) :
      ( p(a)=p(b) ) ⇔ ( Cl_R(a)=Cl_R(b) ) ⇔ R{a,b}.
    Le séquent final = union EXACTE des hypothèses des deux maillons (6 hyps,
    toutes explicites) ; aucune hypothèse neuve ; conclusion ∉ hypothèses.
    g : graphe ; e : ensemble support E ; a, b : points.  Clos modulo
    {R réflexive dans E, R sym, R trans, b∈E, p(a)=Cl_R(a), p(b)=Cl_R(b)}."""
    # A ⇔ B  avec  A = p(a)=p(b),  B = Cl_R(a)=Cl_R(b)
    eqv_p = projection_valeur_classe(g, e, a, b)
    # C ⇔ B  avec  C = R{a,b},     B = Cl_R(a)=Cl_R(b)   (milieu identique)
    eqv_R = relation_ssi_classe_egale(g, a, b, e, x, z)
    # B ⇔ C  puis  A ⇔ C  par transitivité sur le milieu B
    return equivalence_transitivite(eqv_p, equivalence_symetrie(eqv_R))


__all__ = [
    "cible_projection_c55",
    "projection_c55",
]
