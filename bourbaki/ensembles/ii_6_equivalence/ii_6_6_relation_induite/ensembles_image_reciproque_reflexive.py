"""§II.6.6 — Image réciproque S∘φ : relation d'équivalence et réflexivité.

Complète les propriétés de l'image réciproque d'une relation par une application
(E.II.6.6, Déf., `..ensembles_quotient_complements.image_reciproque_relation`).
La symétrie et la transitivité de S∘φ sont déjà acquises
(`image_reciproque_symetrique`, `image_reciproque_transitive`).  On démontre ici,
dans le noyau abrégé (primitives N.* seules ; theorie_ensembles INCHANGÉE = 22) :

  • `image_reciproque_relation_equivalence`  {S sym., S trans.} ⊢ S∘φ relation
        d'équivalence ;
  • `image_reciproque_reflexive`             {S réflexive dans F, φ:E→F} ⊢ (S∘φ)_E
        réflexive dans E.

Stratégie (calquée sur `intersection_relation_equivalence` et sur la réflexivité
de la relation induite, même chapitre) :

  • ÉQUIVALENCE : `conjonction_intro(symétrie, transitivité)` donne LITTÉRALEMENT
    `est_relation_equivalence(S∘φ)` = (S∘φ symétrique ET S∘φ transitive).  Les deux
    lemmes existants partagent les liants x, y (resp. z), si bien que l'assemblage
    coïncide avec la définition d'`ensembles_abrege`.

  • RÉFLEXIVITÉ : la forme gardée (S∘φ)_E{x,x} = (x∈E et x∈E et S{φx,φx}).
    ⇒ : (S∘φ)_E{x,x} donne x∈E (1er conjonct).
    ⇐ : sous x∈E, l'hypothèse φ:E→F donne φ(x)∈F ; la réflexivité de S dans F,
        instanciée en φ(x), donne S{φx,φx} ; on reconstruit (x∈E et x∈E et S{φx,φx}).
    On décharge les deux implications, on assemble l'équivalence (S∘φ)_E{x,x}⇔x∈E,
    on généralise x — d'où VERBATIM `est_reflexive_dans((S∘φ)_E, E)` (liant x).

Les conclusions sont les énoncés EXACTS de `ensembles_abrege` ; les hypothèses
sont exactement les antécédents honnêtes (jamais la conclusion), conformes aux
liants attendus.  Aucun axiome neuf ; toutes les preuves sortent du noyau abrégé.
"""
from __future__ import annotations

from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, impl, appartient, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, equivalence_arriere, instancie)
from bourbaki.ensembles.ii_6_equivalence.ensembles_quotient_complements import (
    image_reciproque_relation, image_reciproque_relation_dans,
    image_reciproque_symetrique, image_reciproque_transitive)


def _tv(t):
    return t if isinstance(t, Terme) else var(t)


# ════════════════════════════════════════════════════════════════════════════
# Théorème 1 — S∘φ relation d'équivalence   (symétrie + transitivité héritées)
# ════════════════════════════════════════════════════════════════════════════
def image_reciproque_relation_equivalence(S=None, phi="phi", x="x", y="y", z="z"):
    """{S symétrique, S transitive} ⊢ S∘φ relation d'équivalence  (E.II.6.6 ; clos mod. hyp.).

    « L'image réciproque d'une relation d'équivalence par une application est une
    relation d'équivalence » : on assemble la symétrie (`image_reciproque_symetrique`,
    mod. {S sym.}) et la transitivité (`image_reciproque_transitive`, mod. {S trans.})
    héritées de S.  Conclusion LITTÉRALEMENT `est_relation_equivalence(S∘φ)`
    (symétrie ET transitivité ; aucune réflexivité requise).  S relation à graphe
    par défaut ; phi terme (graphe de φ).  Clos modulo {S symétrique, S transitive}."""
    if S is None:
        S = E.rel_graphe("GS")
    vphi = _tv(phi)
    sym = image_reciproque_symetrique(S, vphi, x, y)        # (∀x)(∀y)((S∘φ){x,y}⇒(S∘φ){y,x})
    trans = image_reciproque_transitive(S, vphi, x, y, z)   # S∘φ transitive
    return conjonction_intro(sym, trans)                    # est_relation_equivalence(S∘φ)


# ════════════════════════════════════════════════════════════════════════════
# Théorème 2 — (S∘φ)_E réflexive dans E   (héritée de la réflexivité de S dans F)
# ════════════════════════════════════════════════════════════════════════════
def image_reciproque_reflexive(S=None, phi="phi", e="E", f="F", x="x"):
    """{S réflexive dans F, φ:E→F} ⊢ (S∘φ)_E réflexive dans E  (E.II.6.6 ; clos mod. hyp.).

    (S∘φ)_E{x,x} = (x∈E et x∈E et S{φx,φx}).
    ⇒ : (S∘φ)_E{x,x} donne x∈E (1er conjonct).
    ⇐ : sous x∈E, l'hypothèse φ:E→F (codée (∀x)(x∈E ⇒ φ(x)∈F)) donne φ(x)∈F ; la
        réflexivité de S dans F, instanciée en φ(x), donne S{φx,φx} ; on reconstruit
        (x∈E et x∈E et S{φx,φx}).
    L'image réciproque hérite de la réflexivité de S dans F.  S relation à graphe
    par défaut ; phi terme (graphe de φ) ; e = E (= dom φ) ; f = F (= codom φ).
    Clos modulo {S réflexive dans F, φ:E→F}.

    Conclusion littéralement `est_reflexive_dans(image_reciproque_relation_dans(
    S,phi,E), E)` = (∀x)((S∘φ)_E{x,x} ⇔ x∈E) (liant x par défaut)."""
    if S is None:
        S = E.rel_graphe("GS")
    vphi, ve, vf = _tv(phi), _tv(e), _tv(f)
    vx = var(x)
    SP = image_reciproque_relation_dans(S, vphi, ve)
    hrefl = N.assume(E.est_reflexive_dans(S, vf, x))         # (∀a)(S{a,a} ⇔ a∈F)
    happ = N.assume(pourtout(x, impl(appartient(vx, ve),     # φ:E→F : (∀x)(x∈E ⇒ φ(x)∈F)
                                     appartient(E.valeur(vphi, vx), vf))))
    # ⇒ : (S∘φ)_E{x,x} ⇒ x∈E
    h_fwd = N.assume(SP(vx, vx))                             # (x∈E et x∈E) et S{φx,φx}
    xinE_fwd = conjonction_elim_gauche(conjonction_elim_gauche(h_fwd))   # x∈E
    imp_fwd = N.loi_deduction(SP(vx, vx), xinE_fwd)          # (S∘φ)_E{x,x} ⇒ x∈E
    # ⇐ : x∈E ⇒ (S∘φ)_E{x,x}
    h_xinE = N.assume(appartient(vx, ve))                    # x∈E
    phix_inF = N.modus_ponens(h_xinE, instancie(happ, vx))   # φ(x)∈F
    refl_phix = instancie(hrefl, E.valeur(vphi, vx))         # S{φx,φx} ⇔ φx∈F
    sxx = N.modus_ponens(phix_inF, equivalence_arriere(refl_phix))   # S{φx,φx}
    SPxx = conjonction_intro(conjonction_intro(h_xinE, h_xinE), sxx)  # (S∘φ)_E{x,x}
    imp_bwd = N.loi_deduction(appartient(vx, ve), SPxx)      # x∈E ⇒ (S∘φ)_E{x,x}
    eqv = conjonction_intro(imp_fwd, imp_bwd)                # (S∘φ)_E{x,x} ⇔ x∈E
    return N.generalisation(x, eqv)


# ════════════════════════════════════════════════════════════════════════════
# Cibles (reconstruction des conclusions attendues — pour vérification ==)
# ════════════════════════════════════════════════════════════════════════════
def image_reciproque_relation_equivalence_cible(S=None, phi="phi", x="x", y="y", z="z"):
    """Conclusion attendue de `image_reciproque_relation_equivalence` :
    est_relation_equivalence(S∘φ) = (S∘φ symétrique ET S∘φ transitive)."""
    if S is None:
        S = E.rel_graphe("GS")
    SP = image_reciproque_relation(S, _tv(phi))
    return E.est_relation_equivalence(SP, x, y, z)


def image_reciproque_reflexive_cible(S=None, phi="phi", e="E", x="x"):
    """Conclusion attendue de `image_reciproque_reflexive` :
    est_reflexive_dans((S∘φ)_E, E) = (∀x)((S∘φ)_E{x,x} ⇔ x∈E)."""
    if S is None:
        S = E.rel_graphe("GS")
    SP = image_reciproque_relation_dans(S, _tv(phi), _tv(e))
    return E.est_reflexive_dans(SP, _tv(e), x)


__all__ = [
    "image_reciproque_relation_equivalence",
    "image_reciproque_reflexive",
    "image_reciproque_relation_equivalence_cible",
    "image_reciproque_reflexive_cible",
]
