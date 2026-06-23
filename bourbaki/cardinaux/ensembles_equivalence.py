"""§II.6 — Relations d'équivalence : théorèmes certifiés par le noyau abrégé.

Une « relation R{x, y} » est une fonction Python R : (Terme, Terme) → Formule
(cf. ensembles_abrege.est_symetrique/…).  Les définitions verbatim de la section
sont dans ensembles_abrege ; ce module prouve les énoncés directement atteignables :

  • réflexivité partielle d'une relation d'équivalence : sous l'hypothèse que R est
    symétrique et transitive, R{x,y} ⇒ R{x,x}, R{x,y} ⇒ R{y,y}, et donc
    R{x,y} ⇒ (R{x,x} et R{y,y})  (sens ⇒ de l'énoncé de E.II.6.1) ;
  • caractérisation de la classe d'équivalence : (y ∈ Cl_R(x)) ⇔ ((x,y) ∈ G)
    (E.II.6.2 : Cl_R(x) = G⟨{x}⟩ est l'ensemble des y tels que R{x,y}) ;
  • appartenance à l'ensemble quotient E/R (instance de son axiome de définition).

Tout théorème sort du noyau (N.Theoreme clos).  Les propositions lourdes de la
section (C55, C56, C57, décomposition canonique, saturation, produits/quotients de
relations, classes d'objets équivalents) sont REPORTÉES honnêtement (voir __doc__
des fonctions absentes et le rapport) : elles exigent une infrastructure non encore
présente (graphe de l'application canonique comme fonction, images réciproques de
parties, bijections quotient) ou des preuves multi-étapes nouvelles.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, appartient
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (conjonction_intro, equivalence_arriere, instancie)
from bourbaki.ensembles.ii_3_correspondances.ensembles_correspondances import coupe_membre


# ── Réflexivité partielle d'une relation d'équivalence (E.II.6.1) ──────────────
def _sym_inst(hsym, a, b):
    """De ⊢ R symétrique, déduire ⊢ R{a,b} ⇒ R{b,a}  (instance ∀∀)."""
    return instancie(instancie(hsym, a), b)


def _trans_inst(htrans, a, b, c):
    """De ⊢ R transitive, déduire ⊢ (R{a,b} et R{b,c}) ⇒ R{a,c}  (instance ∀∀∀)."""
    return instancie(instancie(instancie(htrans, a), b), c)


def equivalence_reflexive_gauche(R=None, x="x", y="y"):
    """{R symétrique, R transitive} ⊢ R{x,y} ⇒ R{x,x}.   (E.II.6.1.)

    De R{x,y} : symétrie → R{y,x} ; transitivité (R{x,y} et R{y,x}) → R{x,x}."""
    if R is None:
        R = E.rel_graphe("G")
    vx, vy = var(x), var(y)
    hsym = N.assume(E.est_symetrique(R, x, y))
    htrans = N.assume(E.est_transitive(R, x, y))
    h = N.assume(R(vx, vy))                                  # R{x,y}
    ryx = N.modus_ponens(h, _sym_inst(hsym, vx, vy))         # R{y,x}
    rxx = N.modus_ponens(conjonction_intro(h, ryx),
                         _trans_inst(htrans, vx, vy, vx))    # R{x,x}
    return N.loi_deduction(R(vx, vy), rxx)


def equivalence_reflexive_droite(R=None, x="x", y="y"):
    """{R symétrique, R transitive} ⊢ R{x,y} ⇒ R{y,y}.   (E.II.6.1.)

    De R{x,y} : symétrie → R{y,x} ; transitivité (R{y,x} et R{x,y}) → R{y,y}."""
    if R is None:
        R = E.rel_graphe("G")
    vx, vy = var(x), var(y)
    hsym = N.assume(E.est_symetrique(R, x, y))
    htrans = N.assume(E.est_transitive(R, x, y))
    h = N.assume(R(vx, vy))                                  # R{x,y}
    ryx = N.modus_ponens(h, _sym_inst(hsym, vx, vy))         # R{y,x}
    ryy = N.modus_ponens(conjonction_intro(ryx, h),
                         _trans_inst(htrans, vy, vx, vy))    # R{y,y}
    return N.loi_deduction(R(vx, vy), ryy)


def equivalence_reflexive(R=None, x="x", y="y"):
    """{R symétrique, R transitive} ⊢ R{x,y} ⇒ (R{x,x} et R{y,y}).   (E.II.6.1, sens ⇒.)

    C'est le sens ⇒ de l'énoncé « R{x,y} ⇔ (R{x,x} et R{y,y}) » de Bourbaki ; le
    sens ⇐ n'est pas un théorème (faux en général), on ne prouve donc que ⇒."""
    if R is None:
        R = E.rel_graphe("G")
    vx, vy = var(x), var(y)
    h = N.assume(R(vx, vy))
    rxx = N.modus_ponens(h, equivalence_reflexive_gauche(R, x, y))
    ryy = N.modus_ponens(h, equivalence_reflexive_droite(R, x, y))
    return N.loi_deduction(R(vx, vy), conjonction_intro(rxx, ryy))


def symetrie_relation(R=None, x="x", y="y"):
    """{R symétrique} ⊢ R{x,y} ⇒ R{y,x}.   (instance directe de la définition, E.II.6.1.)"""
    if R is None:
        R = E.rel_graphe("G")
    hsym = N.assume(E.est_symetrique(R, x, y))
    return _sym_inst(hsym, var(x), var(y))


def transitivite_relation(R=None, x="x", y="y", z="z"):
    """{R transitive} ⊢ (R{x,y} et R{y,z}) ⇒ R{x,z}.   (instance directe, E.II.6.1.)"""
    if R is None:
        R = E.rel_graphe("G")
    htrans = N.assume(E.est_transitive(R, x, y, z))
    return _trans_inst(htrans, var(x), var(y), var(z))


# ── Classe d'équivalence (E.II.6.2) ───────────────────────────────────────────
def classe_membre(g="G", a="a"):
    """⊢ (y ∈ Cl_R(a)) ⇔ ((a,y) ∈ G).   (E.II.6.2 : Cl_R(a) = G⟨{a}⟩.)

    La classe d'équivalence de a est l'ensemble des y tels que (a,y)∈G, soit, pour
    la relation associée au graphe G, l'ensemble des y tels que R{a,y}.  C'est
    exactement la « coupe » de G suivant a (coupe_membre).  Le point est noté « a »
    (et non « x ») : « x » est le liant interne de l'axiome de l'image directe."""
    return coupe_membre(g, a)


# ── Ensemble quotient E/R (E.II.6.2) ──────────────────────────────────────────
def membre_quotient(g="G", e="E", c="C"):
    """⊢ (C ∈ E/R) ⇔ (C ∈ P(E) et (∃x)(x∈E et C = Cl_R(x))).   (E.II.6.2, instance de l'axiome.)"""
    vg, ve, vc = var(g), var(e), var(c)
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_QUOTIENT)
    return instancie(instancie(instancie(ax, vg), ve), vc)


def classe_dans_quotient(g="G", e="E", a="a"):
    """{a∈E, Cl_R(a)∈P(E)} ⊢ Cl_R(a) ∈ E/R.   (toute classe Cl_R(a), a∈E, est dans E/R.)

    Le témoin x:=a vérifie a∈E et Cl_R(a)=Cl_R(a) (réflexivité)."""
    vg, ve, va = var(g), var(e), var(a)
    cla = E.classe(vg, va)
    # Instancier l'axiome du quotient en C := Cl_R(a)
    car = instancie(instancie(instancie(
        N.axiome(E.theorie_ensembles(), E.AXIOME_QUOTIENT), vg), ve), cla)
    # Construire le membre droit : Cl_R(a)∈P(E) et (∃x)(x∈E et Cl_R(a)=Cl_R(x))
    h_in_parties = N.assume(appartient(cla, E.parties(ve)))  # hyp : Cl_R(a)⊂E ⇒ ∈P(E)
    h_in_e = N.assume(appartient(va, ve))                    # hyp : a∈E
    # témoin x:=a pour (∃x)(x∈E et Cl_R(a)=Cl_R(x))
    corps = et(appartient(var("x"), ve), egal(cla, E.classe(vg, var("x"))))
    temoin = conjonction_intro(h_in_e, N.reflexivite(cla))   # a∈E et Cl_R(a)=Cl_R(a)
    exists = N.modus_ponens(temoin, N.s5(corps, va, "x"))    # (∃x)(x∈E et Cl_R(a)=Cl_R(x))
    droit = conjonction_intro(h_in_parties, exists)
    return N.modus_ponens(droit, equivalence_arriere(car))   # {a∈E, Cl_R(a)∈P(E)} ⊢ Cl_R(a)∈E/R


__all__ = ["equivalence_reflexive_gauche", "equivalence_reflexive_droite",
           "equivalence_reflexive", "symetrie_relation", "transitivite_relation",
           "classe_membre", "membre_quotient", "classe_dans_quotient"]
