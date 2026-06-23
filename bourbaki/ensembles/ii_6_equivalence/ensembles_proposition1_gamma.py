"""§II.6.1 — Proposition 1 (sens réciproque) : conditions sur le graphe G.

Soit Γ une correspondance de X dans X, de graphe G, et R := rel_graphe(G) la
relation associée (R{x,y} := (x,y) ∈ G).  Bourbaki (E.II.6.1, Proposition 1)
caractérise « R est une relation d'équivalence » par trois conditions sur G :

  (a) Δ ⊂ G            ⇔  R réflexive ;
  (b) G = G⁻¹          ⇔  R symétrique ;
  (c) G∘G ⊂ G          ⇔  R transitive.

On formalise ICI le SENS RÉCIPROQUE (de la condition sur G vers la propriété de
R) pour (b) et (c), puis l'assemblage de la condition LOGIQUE d'équivalence
(symétrie ∧ transitivité, déf. `est_relation_equivalence`, E.II.6.1) :

  • `gamma_symetrique_si_egal_reciproque`  {G = G⁻¹}        ⊢ est_symetrique(R) ;
  • `gamma_transitive_si_composee_incluse` {G∘G ⊂ G}       ⊢ est_transitive(R) ;
  • `prop1_reciproque_equivalence`         {G = G⁻¹, G∘G ⊂ G}
        ⊢ est_relation_equivalence(rel_graphe(G)).

NB — la RÉFLEXIVITÉ (a) (Δ ⊂ G) n'est PAS incluse : `est_relation_equivalence`
ne demande que symétrie ∧ transitivité (au sens de Bourbaki, l'équivalence-dans-E
ajoute la réflexivité séparément, cf. `est_relation_equivalence_dans`).  Le volet
(a) est faisable séparément (diagonale Δ) et laissé hors de ce module faible-risque.

STRATÉGIE — preuve sur les GRAPHES de relations (rapide, aucun Card profond) :

  SYMÉTRIE.  Sous G = G⁻¹.  Pour x, y : assume (x,y) ∈ G.  Leibniz (S6) sur
  G = G⁻¹ réécrit (w | w)((x,y)∈w) en l'équivalence (x,y)∈G ⇔ (x,y)∈G⁻¹ ;
  `couple_reciproque(G,x,y)` donne (x,y)∈G⁻¹ ⇔ (y,x)∈G, d'où (y,x) ∈ G.
  loi_deduction + double généralisation (y, x) → est_symetrique(R).

  TRANSITIVITÉ.  Sous G∘G ⊂ G.  Pour x, y, z : assume ((x,y)∈G et (y,z)∈G).
  S5 (témoin y lui-même) → (∃y)((x,y)∈G et (y,z)∈G) ;
  equivalence_arriere(`couple_composee(G,G,x,z)`) → (x,z) ∈ G∘G ;
  instancie l'inclusion G∘G ⊂ G au couple (x,z) → (x,z) ∈ G.
  loi_deduction + triple généralisation (z, y, x) → est_transitive(R).

  ASSEMBLAGE.  conjonction_intro(sym, trans) = est_relation_equivalence(R), de
  séquent {G = G⁻¹, G∘G ⊂ G} (union exacte des deux antécédents, rien postulé,
  conclusion ∉ hypothèses).

Toutes les preuves sortent du noyau abrégé (primitives N.* uniquement, via les deux
maillons `couple_reciproque` / `couple_composee` déjà clos) ; `theorie_ensembles()`
RESTE à 22 axiomes (aucun axiome neuf).

Liants : « x », « y », « z » (les trois points de la sym./trans.) ; « w » (liant
de la réécriture Leibniz S6, frais) ; « y » sert aussi de liant existentiel et de
témoin canonique pour la composée (binder frais, pas de τ-capture sur les couples).
g : graphe G.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et,
                                                           appartient, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_avant, equivalence_arriere, instancie)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque)
from bourbaki.ensembles.fonctions.ii_3_3_composee_graphes.ensembles_composee import (
    couple_composee)


def _t(v):
    """Coercion nom→terme (accepte un Terme ou un nom de variable)."""
    return v if isinstance(v, Terme) else var(v)


# ═════════════════════════════════════════════════════════════════════════════
# Cibles Bourbaki (pour comparer à la conclusion des théorèmes)
# ═════════════════════════════════════════════════════════════════════════════
def cible_symetrique(g="G", x="x", y="y"):
    """Cible (b) : est_symetrique(rel_graphe(G)) = (∀x)(∀y)((x,y)∈G ⇒ (y,x)∈G)."""
    return E.est_symetrique(E.rel_graphe(_t(g)), x, y)


def cible_transitive(g="G", x="x", y="y", z="z"):
    """Cible (c) : est_transitive(rel_graphe(G))
    = (∀x)(∀y)(∀z)(((x,y)∈G et (y,z)∈G) ⇒ (x,z)∈G)."""
    return E.est_transitive(E.rel_graphe(_t(g)), x, y, z)


def cible_equivalence(g="G", x="x", y="y", z="z"):
    """Cible d'assemblage : est_relation_equivalence(rel_graphe(G))
    = est_symetrique(R) ET est_transitive(R)  (condition logique, E.II.6.1)."""
    return E.est_relation_equivalence(E.rel_graphe(_t(g)), x, y, z)


# ═════════════════════════════════════════════════════════════════════════════
# (b)  G = G⁻¹  ⟹  R symétrique
# ═════════════════════════════════════════════════════════════════════════════
def gamma_symetrique_si_egal_reciproque(g="G", x="x", y="y", w="w"):
    """{G = G⁻¹} ⊢ est_symetrique(rel_graphe(G))   (Proposition 1 (b), E.II.6.1).

    Réécriture Leibniz S6 de l'hypothèse G = G⁻¹ : (x,y)∈G ⇔ (x,y)∈G⁻¹, puis
    `couple_reciproque` : (x,y)∈G⁻¹ ⇔ (y,x)∈G ; clôture universelle sur (x,y)∈G.
    Clos modulo la seule hypothèse load-bearing G = G⁻¹ ; conclusion ∉ hypothèses.
    Liant frais « w » pour la substitution Leibniz."""
    vg = _t(g)
    vx, vy = _t(x), _t(y)
    grec = E.reciproque(vg)

    hyp_eg = N.assume(egal(vg, grec))                       # G = G⁻¹
    hxy = N.assume(appartient(E.couple(vx, vy), vg))        # (x,y) ∈ G

    # Leibniz S6 : (G = G⁻¹) ⇒ ((w|w)(x,y)∈w  ⇔  (w|w)(x,y)∈w) sur G, G⁻¹
    leibniz = N.s6(vg, grec, w, appartient(E.couple(vx, vy), var(w)))
    eqv_g_grec = N.modus_ponens(hyp_eg, leibniz)            # (x,y)∈G ⇔ (x,y)∈G⁻¹
    xy_in_rec = N.modus_ponens(hxy, equivalence_avant(eqv_g_grec))   # (x,y) ∈ G⁻¹

    cr = couple_reciproque(g, x, y)                         # (x,y)∈G⁻¹ ⇔ (y,x)∈G
    yx_in_g = N.modus_ponens(xy_in_rec, equivalence_avant(cr))       # (y,x) ∈ G

    impl_xy = N.loi_deduction(appartient(E.couple(vx, vy), vg), yx_in_g)
    return N.generalisation(x, N.generalisation(y, impl_xy))


# ═════════════════════════════════════════════════════════════════════════════
# (c)  G∘G ⊂ G  ⟹  R transitive
# ═════════════════════════════════════════════════════════════════════════════
def gamma_transitive_si_composee_incluse(g="G", x="x", y="y", z="z"):
    """{G∘G ⊂ G} ⊢ est_transitive(rel_graphe(G))   (Proposition 1 (c), E.II.6.1).

    De (x,y)∈G et (y,z)∈G : S5 (témoin y lui-même) donne (∃y)((x,y)∈G et (y,z)∈G),
    soit, par `couple_composee(G,G,x,z)`, (x,z)∈G∘G ; l'inclusion G∘G ⊂ G,
    instanciée au couple (x,z), conclut (x,z)∈G.  Clôture universelle sur l'hypothèse
    conjointe.  Clos modulo la seule hypothèse G∘G ⊂ G ; conclusion ∉ hypothèses.
    Le liant existentiel/témoin « y » est frais (pas de τ-capture sur la composée)."""
    vg = _t(g)
    vx, vy, vz = _t(x), _t(y), _t(z)
    gg = E.composee(vg, vg)

    hincl = N.assume(inclus(gg, vg))                        # G∘G ⊂ G
    xy = appartient(E.couple(vx, vy), vg)                   # (x,y) ∈ G
    yz = appartient(E.couple(vy, vz), vg)                   # (y,z) ∈ G
    hconj = N.assume(et(xy, yz))                            # (x,y)∈G et (y,z)∈G

    # S5 : témoin = y lui-même → (∃y)((x,y)∈G et (y,z)∈G)
    ex_body = N.modus_ponens(hconj, N.s5(et(xy, yz), vy, y))
    # couple_composee : ((x,z)∈G∘G) ⇔ (∃y)((x,y)∈G et (y,z)∈G)  (G'=G)
    cc = couple_composee(g, g, x, z)
    xz_in_gg = N.modus_ponens(ex_body, equivalence_arriere(cc))     # (x,z) ∈ G∘G

    # instancie l'inclusion au couple (x,z) : (x,z)∈G∘G ⇒ (x,z)∈G
    inst = instancie(hincl, E.couple(vx, vz))
    xz_in_g = N.modus_ponens(xz_in_gg, inst)               # (x,z) ∈ G

    impl_conj = N.loi_deduction(et(xy, yz), xz_in_g)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, impl_conj)))


# ═════════════════════════════════════════════════════════════════════════════
# Assemblage — {G = G⁻¹, G∘G ⊂ G} ⊢ est_relation_equivalence(R)
# ═════════════════════════════════════════════════════════════════════════════
def prop1_reciproque_equivalence(g="G", x="x", y="y", z="z", w="w"):
    """{G = G⁻¹, G∘G ⊂ G} ⊢ est_relation_equivalence(rel_graphe(G)).

    Sens RÉCIPROQUE de la Proposition 1 (E.II.6.1), volet logique : sous ces deux
    conditions sur le graphe G, la relation R := rel_graphe(G) est SYMÉTRIQUE (b)
    et TRANSITIVE (c), donc une relation d'équivalence au sens de la définition
    `est_relation_equivalence` (symétrie ∧ transitivité).

    PUR ASSEMBLAGE des deux maillons clos modulo hypothèses :
      sym   : {G = G⁻¹}  ⊢ est_symetrique(R)   (gamma_symetrique_si_egal_reciproque) ;
      trans : {G∘G ⊂ G}  ⊢ est_transitive(R)   (gamma_transitive_si_composee_incluse) ;
      conjonction_intro(sym, trans) = est_relation_equivalence(R).

    Le séquent final = union EXACTE des deux antécédents (2 hypothèses, toutes
    explicites et load-bearing) ; aucune hypothèse neuve ; conclusion ∉ hypothèses.
    La RÉFLEXIVITÉ (a) (Δ ⊂ G) n'entre PAS (hors de la condition logique)."""
    sym = gamma_symetrique_si_egal_reciproque(g, x, y, w)
    trans = gamma_transitive_si_composee_incluse(g, x, y, z)
    return conjonction_intro(sym, trans)


__all__ = [
    "cible_symetrique",
    "cible_transitive",
    "cible_equivalence",
    "gamma_symetrique_si_egal_reciproque",
    "gamma_transitive_si_composee_incluse",
    "prop1_reciproque_equivalence",
]
