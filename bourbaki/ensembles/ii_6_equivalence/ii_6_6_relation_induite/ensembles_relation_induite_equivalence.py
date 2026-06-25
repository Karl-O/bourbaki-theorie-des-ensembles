"""§II.6.6 — R_A transitive et R_A relation d'équivalence (héritées de R).

Complète les propriétés de la relation induite R_A{x,y} := (x∈A et y∈A et R{x,y})
(E.II.6.6, Déf., `..ensembles_quotient_complements.relation_induite`).  La symétrie
de R_A est déjà acquise (`relation_induite_symetrique`).  On démontre ici, dans le
noyau abrégé (primitives N.* seules ; theorie_ensembles INCHANGÉE = 22) :

  • `relation_induite_transitive`           {R transitive} ⊢ R_A transitive ;
  • `relation_induite_relation_equivalence` {R sym., R trans.} ⊢ R_A relation
        d'équivalence.

Stratégie (calquée sur `image_reciproque_transitive` et `intersection_relation_
equivalence` du même chapitre) :

  • TRANSITIVITÉ : sous (R_A{x,y} et R_A{y,z}), on extrait x∈A (gauche de R_A{x,y}),
    z∈A (droite des appartenances de R_A{y,z}), R{x,y} et R{y,z} ; la transitivité
    de R (hypothèse, instanciée en x,y,z) donne R{x,z} ; on reconstruit
    R_A{x,z} = ((x∈A et z∈A) et R{x,z}), on décharge l'implication, on généralise
    z, y, x — d'où VERBATIM `est_transitive(R_A)` (liants x, y, z).

  • ÉQUIVALENCE : `conjonction_intro(symétrie, transitivité)` donne LITTÉRALEMENT
    `est_relation_equivalence(R_A)` = (R_A symétrique ET R_A transitive).  Les deux
    lemmes partagent les liants x, y (resp. z), si bien que l'assemblage coïncide
    avec la définition d'`ensembles_abrege`.

Les conclusions sont les énoncés EXACTS de `ensembles_abrege` ; les hypothèses
sont exactement les antécédents honnêtes (jamais la conclusion), conformes aux
liants attendus.
"""
from __future__ import annotations

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import Terme, var, et
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie)
from bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_complements import (
    relation_induite, relation_induite_symetrique)


def _tv(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
# Théorème 1 — R_A transitive   (hérite de la transitivité de R)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §6.6 Def.- | E II.45 L.9-11 | PDF p.96
def relation_induite_transitive(R=None, a="A", x="x", y="y", z="z"):
    """{R transitive} ⊢ (∀x)(∀y)(∀z)((R_A{x,y} et R_A{y,z}) ⇒ R_A{x,z})
    (R_A transitive ; clos mod. hyp.).

    R_A{x,y} et R_A{y,z} = ((x∈A et y∈A) et R{x,y}) et ((y∈A et z∈A) et R{y,z}) ;
    on extrait x∈A, z∈A, R{x,y}, R{y,z} ; la transitivité de R en (x,y,z) donne
    R{x,z}, d'où R_A{x,z} = ((x∈A et z∈A) et R{x,z}).  La relation induite hérite
    de la transitivité de R.  R relation à graphe par défaut ; A terme.  Clos
    modulo {R transitive}.

    Conclusion littéralement `est_transitive(relation_induite(R,A))` (liants x,y,z
    par défaut, identiques à ceux d'`ensembles_abrege.est_transitive`)."""
    if R is None:
        R = E.rel_graphe("GR")
    va = _tv(a)
    vx, vy, vz = var(x), var(y), var(z)
    RA = relation_induite(R, va)
    htr = N.assume(E.est_transitive(R, "a", "b", "c"))   # (∀a)(∀b)(∀c)((R{a,b}et R{b,c})⇒R{a,c})
    h = N.assume(et(RA(vx, vy), RA(vy, vz)))             # R_A{x,y} et R_A{y,z}
    h_xy = conjonction_elim_gauche(h)                    # (x∈A et y∈A) et R{x,y}
    h_yz = conjonction_elim_droite(h)                    # (y∈A et z∈A) et R{y,z}
    hx_A = conjonction_elim_gauche(conjonction_elim_gauche(h_xy))   # x∈A
    hz_A = conjonction_elim_droite(conjonction_elim_gauche(h_yz))   # z∈A
    rxy = conjonction_elim_droite(h_xy)                  # R{x,y}
    ryz = conjonction_elim_droite(h_yz)                  # R{y,z}
    imp = instancie(instancie(instancie(htr, vx), vy), vz)   # (R{x,y}et R{y,z})⇒R{x,z}
    rxz = N.modus_ponens(conjonction_intro(rxy, ryz), imp)   # R{x,z}
    but = conjonction_intro(conjonction_intro(hx_A, hz_A), rxz)   # R_A{x,z}
    dimp = N.loi_deduction(et(RA(vx, vy), RA(vy, vz)), but)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, dimp)))


# ════════════════════════════════════════════════════════════════════════════
# Théorème 2 — R_A relation d'équivalence   (symétrie + transitivité héritées)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §6.6 Def.- | E II.45 L.9-11 | PDF p.96
def relation_induite_relation_equivalence(R=None, a="A", x="x", y="y", z="z"):
    """{R symétrique, R transitive} ⊢ R_A relation d'équivalence  (E.II.6.6 ; clos mod. hyp.).

    « La relation induite par une relation d'équivalence sur une partie A est une
    relation d'équivalence » : on assemble la symétrie (`relation_induite_symetrique`,
    mod. {R sym.}) et la transitivité (`relation_induite_transitive`, mod. {R trans.})
    héritées de R.  Conclusion LITTÉRALEMENT `est_relation_equivalence(R_A)`
    (symétrie ET transitivité ; aucune réflexivité requise).  R relation à graphe
    par défaut ; A terme.  Clos modulo {R symétrique, R transitive}."""
    if R is None:
        R = E.rel_graphe("GR")
    va = _tv(a)
    sym = relation_induite_symetrique(R, va, x, y)       # (∀x)(∀y)(R_A{x,y}⇒R_A{y,x})
    trans = relation_induite_transitive(R, va, x, y, z)  # R_A transitive
    return conjonction_intro(sym, trans)                 # est_relation_equivalence(R_A)


# ════════════════════════════════════════════════════════════════════════════
# Cibles (reconstruction des conclusions attendues — pour vérification ==)
# ════════════════════════════════════════════════════════════════════════════
def relation_induite_transitive_cible(R=None, a="A", x="x", y="y", z="z"):
    """Conclusion attendue de `relation_induite_transitive` : est_transitive(R_A)."""
    if R is None:
        R = E.rel_graphe("GR")
    RA = relation_induite(R, _tv(a))
    return E.est_transitive(RA, x, y, z)


def relation_induite_relation_equivalence_cible(R=None, a="A", x="x", y="y", z="z"):
    """Conclusion attendue de `relation_induite_relation_equivalence` :
    est_relation_equivalence(R_A) = (R_A symétrique ET R_A transitive)."""
    if R is None:
        R = E.rel_graphe("GR")
    RA = relation_induite(R, _tv(a))
    return E.est_relation_equivalence(RA, x, y, z)


__all__ = [
    "relation_induite_transitive",
    "relation_induite_relation_equivalence",
    "relation_induite_transitive_cible",
    "relation_induite_relation_equivalence_cible",
]
