"""§II.3.2 — INVOLUTION de la réciproque : (G⁻¹)⁻¹ = G  (Bourbaki E II.11, Déf. 5).

Énoncé Bourbaki VERBATIM (E II.11, §3, n°2, Définition 5) :

  « Il est évident que le graphe réciproque de G⁻¹ est G. »

soit, en notation graphe :  (G⁻¹)⁻¹ = G.

RÉSULTAT (CLOS SOUS HYPOTHÈSE HONNÊTE — certifié par le noyau LCF) :

  { est_graphe(G) }  ⊢  reciproque(reciproque(G)) = G

où  est_graphe(G) := (∀z)(z ∈ G ⇒ (∃a)(∃b)(z = (a, b)))  (E II.7 ; « G est un
ensemble de couples »), prédicat importé de `ensembles_graphe_inclus_produit`.

POURQUOI est_graphe EST LOAD-BEARING.  Le graphe réciproque (G⁻¹ = E.reciproque)
ne CONTIENT QUE des couples (par construction, AXIOME_RECIP : z∈G⁻¹ ⇔ (∃p)(∃q)
(z=(p,q) et (q,p)∈G)) — donc (G⁻¹)⁻¹ aussi.  L'inclusion (G⁻¹)⁻¹ ⊂ G est ainsi
INCONDITIONNELLE.  Mais l'inclusion réciproque G ⊂ (G⁻¹)⁻¹ exige que TOUT z∈G
soit un couple (sinon un z∈G non-couple n'apparaît jamais dans (G⁻¹)⁻¹).  C'est
exactement l'hypothèse de Bourbaki (« Soit G un GRAPHE », Déf. 5) : elle ne contient
pas la conclusion → clôture conditionnelle HONNÊTE.

STRATÉGIE (extensionnalité A1 = double inclusion ; tout au niveau couple).
Caractérisation utilisée : ((u,v) ∈ H⁻¹) ⇔ ((v,u) ∈ H)  (`couple_reciproque`) et
z∈H⁻¹ ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈H)  (`_inst_recip` = AXIOME_RECIP).

  ⊂  (INCONDITIONNEL) : z∈(G⁻¹)⁻¹ ⇒ (∃p)(∃q)(z=(p,q) et (q,p)∈G⁻¹).  De (q,p)∈G⁻¹,
     couple_reciproque(G,q,p) donne (p,q)∈G ; z=(p,q) [S6] ⇒ z∈G.  ∃-élim p, q.
  ⊃  (SOUS est_graphe) : z∈G ⇒ (est_graphe) (∃a)(∃b)(z=(a,b)).  De z=(a,b) [S6] :
     (a,b)∈G ; couple_reciproque(G,b,a) ⇒ (b,a)∈G⁻¹ ; couple_reciproque(G⁻¹,a,b) ⇒
     (a,b)∈(G⁻¹)⁻¹ ; z=(a,b) [S6] ⇒ z∈(G⁻¹)⁻¹.  ∃-élim a, b.

  extensionnalite_appliquee((G⁻¹)⁻¹, G) sur (⊂ et ⊃) ; on GARDE est_graphe(G)
  comme hypothèse non déchargée (clôture conditionnelle).

theorie_ensembles() INCHANGÉE (= 22) : aucun axiome ajouté (primitives N.* seules,
réutilisation de couple_reciproque / est_graphe / extensionnalite_appliquee).

Les liants p, q (de AXIOME_RECIP) et a, b (de est_couple/est_graphe) sont disjoints
— pas de capture lors des ∃-éliminations (calque de `couple_reciproque`).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (
    Terme, var, egal, et, impl, appartient, existe, inclus)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, equivalence_transitivite, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, congruence_existe)
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import (
    extensionnalite_appliquee)
from bourbaki.ensembles.fonctions.ii_3_2_reciproque.ensembles_reciproque import (
    couple_reciproque)
from bourbaki.ensembles.ii_3_correspondances.ensembles_graphe_inclus_produit import (
    est_graphe)


def _T(v):
    """Coercion nom → terme."""
    return v if isinstance(v, Terme) else var(v)


def _inst_recip(g, z):
    """⊢ (z ∈ G⁻¹) ⇔ (∃p)(∃q)(z = (p, q) et (q, p) ∈ G).   (instance de AXIOME_RECIP.)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_RECIP)
    return instancie(instancie(ax, g), z)


def _involution_incluse(vg):
    """⊢ (G⁻¹)⁻¹ ⊂ G.   (INCONDITIONNEL : (G⁻¹)⁻¹ ne contient que des couples de G.)

    z∈(G⁻¹)⁻¹ ⇒ (∃p)(∃q)(z=(p,q) et (q,p)∈G⁻¹) [AXIOME_RECIP sur G⁻¹] ; on α-renomme
    les liants p,q → r,s (≠ p,q internes de couple_reciproque, cf. comparabilite) ;
    sous (r,s) : (s,r)∈G⁻¹ ⇒ (r,s)∈G [couple_reciproque(G,s,r)] ; z=(r,s) [S6] ⇒ z∈G ;
    ∃-élim s puis r."""
    vz = var("z")
    Grec = E.reciproque(vg)
    Grr = E.reciproque(Grec)
    vr, vs = var("r"), var("s")

    # AXIOME_RECIP sur G⁻¹ : z∈(G⁻¹)⁻¹ ⇔ (∃p)(∃q)(z=(p,q) et (q,p)∈G⁻¹), liants p,q.
    rec0 = _inst_recip(Grec, vz)
    # α-renomme p→r puis q→s (les witnesses r,s ≠ p,q internes de couple_reciproque).
    body_pq = et(egal(vz, E.couple(var("p"), var("q"))),
                 appartient(E.couple(var("q"), var("p")), Grec))
    rec1 = equivalence_transitivite(rec0, alpha_existe("p", "r", existe("q", body_pq)))
    body_rq = et(egal(vz, E.couple(vr, var("q"))),
                 appartient(E.couple(var("q"), vr), Grec))
    rec = equivalence_transitivite(rec1, congruence_existe(alpha_existe("q", "s", body_rq), "r"))
    body = et(egal(vz, E.couple(vr, vs)), appartient(E.couple(vs, vr), Grec))  # liants r,s

    # sous {body} : z = (r,s) et (s,r)∈G⁻¹ ⊢ z∈G
    hb = N.assume(body)
    rs_in_g = N.modus_ponens(conjonction_elim_droite(hb),          # (s,r)∈G⁻¹
                             equivalence_avant(couple_reciproque(vg, "s", "r")))  # ⇒ (r,s)∈G
    # S6 : (z=(r,s)) ⇒ ((z∈G) ⇔ ((r,s)∈G)) ; sens ⇐ + MP((r,s)∈G) ⇒ z∈G
    z_iff = N.modus_ponens(conjonction_elim_gauche(hb),
                           N.s6(vz, E.couple(vr, vs), "w", appartient(var("w"), vg)))
    z_in_g = N.modus_ponens(rs_in_g, equivalence_arriere(z_iff))   # {body} ⊢ z∈G
    # décharger body, ∃-éliminer s puis r (z∈G sans r,s libres → propre)
    imp_body = N.loi_deduction(body, z_in_g)
    elim = existe_elimination(existe_elimination(imp_body, "s"), "r")  # (∃r)(∃s)body ⇒ z∈G

    h_z = N.assume(appartient(vz, Grr))                           # z∈(G⁻¹)⁻¹
    z_in_g2 = N.modus_ponens(N.modus_ponens(h_z, equivalence_avant(rec)), elim)  # {z∈Grr} ⊢ z∈G
    imp = N.loi_deduction(appartient(vz, Grr), z_in_g2)           # ⊢ (z∈Grr ⇒ z∈G)
    return N.generalisation("z", imp)                            # ⊢ (G⁻¹)⁻¹ ⊂ G


def _involution_contient(vg):
    """{ est_graphe(G) } ⊢ G ⊂ (G⁻¹)⁻¹.   (CONDITIONNEL : tout z∈G doit être un couple.)

    z∈G ⇒ (est_graphe) (∃a)(∃b)(z=(a,b)) ; sous (a,b) : (a,b)∈G [S6] ⇒ (b,a)∈G⁻¹
    [couple_reciproque(G,b,a) sens ⇐] ⇒ (a,b)∈(G⁻¹)⁻¹ [couple_reciproque(G⁻¹,a,b) ⇐] ;
    z=(a,b) [S6] ⇒ z∈(G⁻¹)⁻¹ ; ∃-élim a,b.  est_graphe(G) GARDÉE."""
    vz = var("z")
    Grec = E.reciproque(vg)
    Grr = E.reciproque(Grec)
    va, vb = var("a"), var("b")
    cpl = E.couple(va, vb)

    h_graphe = N.assume(est_graphe(vg))                          # (∀z)(z∈G ⇒ (∃a)(∃b)z=(a,b))
    h_z = N.assume(appartient(vz, vg))                           # z∈G
    ec = N.modus_ponens(h_z, instancie(h_graphe, vz))            # (∃a)(∃b)(z=(a,b))

    # sous { z=(a,b) } : z∈G ⊢ z∈(G⁻¹)⁻¹
    h_eq = N.assume(egal(vz, cpl))                              # z = (a,b)
    # (a,b)∈G  [S6 sur z∈G]
    zc_iff = N.modus_ponens(h_eq, N.s6(vz, cpl, "w", appartient(var("w"), vg)))
    ab_in_g = N.modus_ponens(h_z, equivalence_avant(zc_iff))     # {z∈G, z=(a,b)} ⊢ (a,b)∈G
    # (b,a)∈G⁻¹  [couple_reciproque(G,b,a) : (b,a)∈G⁻¹ ⇔ (a,b)∈G, sens ⇐]
    ba_in_grec = N.modus_ponens(ab_in_g,
                                equivalence_arriere(couple_reciproque(vg, "b", "a")))
    # (a,b)∈(G⁻¹)⁻¹  [couple_reciproque(G⁻¹,a,b) : (a,b)∈(G⁻¹)⁻¹ ⇔ (b,a)∈G⁻¹, sens ⇐]
    ab_in_grr = N.modus_ponens(ba_in_grec,
                               equivalence_arriere(couple_reciproque(Grec, "a", "b")))
    # z∈(G⁻¹)⁻¹  [S6, z=(a,b), sens ⇐]
    zc_iff_grr = N.modus_ponens(h_eq, N.s6(vz, cpl, "w", appartient(var("w"), Grr)))
    z_in_grr = N.modus_ponens(ab_in_grr, equivalence_arriere(zc_iff_grr))  # z∈(G⁻¹)⁻¹

    # décharger z=(a,b), ∃-éliminer b puis a (conséquent z∈Grr sans a,b → propre)
    imp_eq = N.loi_deduction(egal(vz, cpl), z_in_grr)            # {z∈G} ⊢ (z=(a,b) ⇒ z∈Grr)
    elim = existe_elimination(existe_elimination(imp_eq, "b"), "a")  # (∃a)(∃b)z=(a,b) ⇒ z∈Grr
    z_in_grr2 = N.modus_ponens(ec, elim)                        # {est_graphe G, z∈G} ⊢ z∈Grr
    imp = N.loi_deduction(appartient(vz, vg), z_in_grr2)        # {est_graphe G} ⊢ (z∈G ⇒ z∈Grr)
    return N.generalisation("z", imp)                          # {est_graphe G} ⊢ G ⊂ (G⁻¹)⁻¹


# @livre Ch.II §3.2 Def.5 | E II.11 L.16-17 | PDF p.62
def reciproque_involution(g="G"):
    """{ est_graphe(G) } ⊢ (G⁻¹)⁻¹ = G.   (Bourbaki E II.11, Déf. 5.)

    « Il est évident que le graphe réciproque de G⁻¹ est G. »  Clos SOUS l'hypothèse
    honnête est_graphe(G) (= « G est un graphe »), conservée non déchargée.
    (G⁻¹)⁻¹ ⊂ G est inconditionnel ; G ⊂ (G⁻¹)⁻¹ requiert est_graphe(G)."""
    vg = _T(g)
    Grr = E.reciproque(E.reciproque(vg))
    incl = _involution_incluse(vg)                              # ⊢ (G⁻¹)⁻¹ ⊂ G
    cont = _involution_contient(vg)                             # {est_graphe G} ⊢ G ⊂ (G⁻¹)⁻¹
    ext = extensionnalite_appliquee(Grr, vg)                    # ((G⁻¹)⁻¹⊂G et G⊂(G⁻¹)⁻¹) ⇒ (G⁻¹)⁻¹=G
    return N.modus_ponens(conjonction_intro(incl, cont), ext)  # {est_graphe G} ⊢ (G⁻¹)⁻¹ = G


def reciproque_involution_cible(g="G"):
    """Énoncé visé de `reciproque_involution` (pour vérification stricte) : (G⁻¹)⁻¹ = G."""
    vg = _T(g)
    return egal(E.reciproque(E.reciproque(vg)), vg)


__all__ = ["reciproque_involution", "reciproque_involution_cible"]
