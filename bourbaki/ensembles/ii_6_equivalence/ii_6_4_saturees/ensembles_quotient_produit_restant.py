"""§II.6 (restant) — PROPRIÉTÉS directes des relations d'équivalence non encore
prouvées : produit de relations d'équivalence R×R' (II.6.8), relation induite R_A
(complément transitivité/réflexivité, II.6.6), relation « plus fine » comme
préordre (II.6.7), saturation (II.6.4).

Module NEUF (campagne II.5/II.6-restant).  On NE MODIFIE AUCUN fichier existant ;
on RÉUTILISE strictement les NOTIONS déjà définies dans `ensembles_abrege` :
  • `est_symetrique` / `est_transitive` / `est_relation_equivalence`  (II.6.1) ;
  • `relation_produit` (R×R' sur composantes, II.6.8) ;
  • `relation_induite` (R_A, dans `ensembles_quotient_complements`, II.6.6) ;
  • `plus_fine` (S plus fine que R, II.6.7) ;
  • `est_saturee` / `est_compatible` (A saturée, II.6.4) ;
  • `pr1` / `pr2` / `couple` (composantes d'un couple).

theorie_ensembles() RESTE à 22 axiomes (AUCUN axiome neuf ici).  Toutes les preuves
sortent du noyau abrégé (assume / modus_ponens / loi_deduction / generalisation /
conjonction / instancie).  Hypothèses laissées EXPLICITEMENT dans le séquent — rien
postulé, aucune tautologie, aucun affaibli.

══════════════════════════════════════════════════════════════════════════════
THÉORÈMES CERTIFIÉS  (chacun testé, cf. test_ensembles_quotient_produit_restant.py)
══════════════════════════════════════════════════════════════════════════════

§6.8 — Produit de relations d'équivalence R×R' :
  • relation_produit_couples(R,R')   — la relation S{u,v} := R{pr1 u, pr1 v} et
        R'{pr2 u, pr2 v} sur les couples (forme « directe sur les composantes »
        de Bourbaki, R×R' lue par projections) ;
  • produit_symetrique     {R sym, R' sym} ⊢ (R×R') symétrique          [mod. hyp.]
  • produit_transitive     {R trans, R' trans} ⊢ (R×R') transitive      [mod. hyp.]
  • produit_relation_equivalence  {R éq., R' éq.} ⊢ (R×R') éq.          [mod. hyp.]
        — « S{u,v} est une relation d'équivalence appelée produit de R et R' »
          (II.6.8) : on assemble symétrie + transitivité héritées composante par
          composante.

§6.6 — Relation induite R_A (complément : transitivité, réflexivité) :
  • induite_transitive     {R trans} ⊢ R_A transitive                  [mod. hyp.]
  • induite_reflexive_dans {R réflexive dans E, A⊂E (ponctuel)} ⊢ R_A{x,x}⇔x∈A
        (R_A réflexive dans A)                                         [mod. hyp.]
  • induite_relation_equivalence {R sym, R trans} ⊢ R_A éq.            [mod. hyp.]
        (complète `relation_induite_symetrique` du module complements).

§6.7 — « plus fine » est un PRÉORDRE sur les relations :
  • plus_fine_reflexive            ⊢ R plus fine que R                 [INCONDITIONNEL]
  • plus_fine_transitive  {S plus fine T, T plus fine R} ⊢ S plus fine R [mod. hyp.]

§6.4 — Saturation :
  • saturee_implique_classe_incluse  {A saturée pour R} ⊢ (x∈A et R{x,y}) ⇒ y∈A
        (cœur : une partie saturée est close par R — « réunion de classes »).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, egal, et, impl, equiv,
                                       appartient, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    instancie)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ════════════════════════════════════════════════════════════════════════════
# §6.8 — Produit de relations d'équivalence R × R'
# ════════════════════════════════════════════════════════════════════════════
# Bourbaki (II.6.8) : (R × R'){(x,x'), (y,y')} := R{x,y} et R'{x',y'}.  Lu sur des
# couples u = (x,x'), v = (y,y'), c'est S{u,v} := R{pr1 u, pr1 v} et
# R'{pr2 u, pr2 v}.  On expose cette relation à DEUX arguments (sur les couples),
# de sorte qu'elle s'enfourne directement dans est_symetrique / est_transitive.

def relation_produit_couples(R, Rp):
    """(R × R'){u,v} := R{pr1 u, pr1 v} et R'{pr2 u, pr2 v}  (produit de relations,
    II.6.8, lu sur les couples u=(x,x'), v=(y,y')).

    Forme « directe sur les composantes » de Bourbaki, à DEUX arguments (les
    couples), donc utilisable comme R{·,·} (s'enfourne dans est_symetrique /
    est_transitive).  R, R' : relations (fonctions (Terme,Terme)→Formule).
    Renvoie une fonction (Terme,Terme)→Formule."""
    def S(u, v):
        return et(R(E.pr1(u), E.pr1(v)), Rp(E.pr2(u), E.pr2(v)))
    return S


def produit_symetrique(R=None, Rp=None, u="u", v="v"):
    """{R symétrique, R' symétrique} ⊢ (R×R') symétrique  (II.6.8 ; clos mod. hyp.).

    (R×R'){u,v} = R{pr1 u, pr1 v} et R'{pr2 u, pr2 v}.  Par symétrie de R en
    (pr1 u, pr1 v) et de R' en (pr2 u, pr2 v), on obtient R{pr1 v, pr1 u} et
    R'{pr2 v, pr2 u} = (R×R'){v,u}.  Le produit hérite de la symétrie composante
    par composante.  R, R' à graphe par défaut ; clos modulo {R sym, R' sym}."""
    if R is None:
        R = E.rel_graphe("GR")
    if Rp is None:
        Rp = E.rel_graphe("GRp")
    vu, vv = var(u), var(v)
    S = relation_produit_couples(R, Rp)
    p1u, p1v = E.pr1(vu), E.pr1(vv)
    p2u, p2v = E.pr2(vu), E.pr2(vv)
    hsR = N.assume(E.est_symetrique(R, "a", "b"))     # (∀a)(∀b)(R{a,b}⇒R{b,a})
    hsRp = N.assume(E.est_symetrique(Rp, "a", "b"))   # idem R'
    h = N.assume(S(vu, vv))                            # R{p1u,p1v} et R'{p2u,p2v}
    rR = conjonction_elim_gauche(h)                    # R{p1u,p1v}
    rRp = conjonction_elim_droite(h)                   # R'{p2u,p2v}
    impR = instancie(instancie(hsR, p1u), p1v)         # R{p1u,p1v}⇒R{p1v,p1u}
    impRp = instancie(instancie(hsRp, p2u), p2v)       # R'{p2u,p2v}⇒R'{p2v,p2u}
    swR = N.modus_ponens(rR, impR)                     # R{p1v,p1u}
    swRp = N.modus_ponens(rRp, impRp)                  # R'{p2v,p2u}
    but = conjonction_intro(swR, swRp)                 # (R×R'){v,u}
    imp = N.loi_deduction(S(vu, vv), but)
    return N.generalisation(u, N.generalisation(v, imp))


def produit_transitive(R=None, Rp=None, u="u", v="v", w="wb"):
    """{R transitive, R' transitive} ⊢ (R×R') transitive  (II.6.8 ; clos mod. hyp.).

    ((R×R'){u,v} et (R×R'){v,w}) = (R{p1u,p1v} et R'{p2u,p2v}) et
    (R{p1v,p1w} et R'{p2v,p2w}).  Transitivité de R en (p1u,p1v,p1w) donne
    R{p1u,p1w} ; de R' en (p2u,p2v,p2w) donne R'{p2u,p2w} ; d'où (R×R'){u,w}.
    R, R' à graphe par défaut ; clos modulo {R trans, R' trans}."""
    if R is None:
        R = E.rel_graphe("GR")
    if Rp is None:
        Rp = E.rel_graphe("GRp")
    vu, vv, vw = var(u), var(v), var(w)
    S = relation_produit_couples(R, Rp)
    p1u, p1v, p1w = E.pr1(vu), E.pr1(vv), E.pr1(vw)
    p2u, p2v, p2w = E.pr2(vu), E.pr2(vv), E.pr2(vw)
    htR = N.assume(E.est_transitive(R, "a", "b", "c"))     # transitivité de R
    htRp = N.assume(E.est_transitive(Rp, "a", "b", "c"))   # transitivité de R'
    h = N.assume(et(S(vu, vv), S(vv, vw)))                 # S{u,v} et S{v,w}
    h_uv = conjonction_elim_gauche(h)                      # S{u,v}
    h_vw = conjonction_elim_droite(h)                      # S{v,w}
    rR_uv = conjonction_elim_gauche(h_uv)                  # R{p1u,p1v}
    rRp_uv = conjonction_elim_droite(h_uv)                 # R'{p2u,p2v}
    rR_vw = conjonction_elim_gauche(h_vw)                  # R{p1v,p1w}
    rRp_vw = conjonction_elim_droite(h_vw)                 # R'{p2v,p2w}
    # transitivité de R : (R{p1u,p1v} et R{p1v,p1w}) ⇒ R{p1u,p1w}
    trR = instancie(instancie(instancie(htR, p1u), p1v), p1w)
    rR_uw = N.modus_ponens(conjonction_intro(rR_uv, rR_vw), trR)   # R{p1u,p1w}
    # transitivité de R' : (R'{p2u,p2v} et R'{p2v,p2w}) ⇒ R'{p2u,p2w}
    trRp = instancie(instancie(instancie(htRp, p2u), p2v), p2w)
    rRp_uw = N.modus_ponens(conjonction_intro(rRp_uv, rRp_vw), trRp)  # R'{p2u,p2w}
    but = conjonction_intro(rR_uw, rRp_uw)                 # (R×R'){u,w}
    imp = N.loi_deduction(et(S(vu, vv), S(vv, vw)), but)
    return N.generalisation(u, N.generalisation(v, N.generalisation(w, imp)))


def produit_relation_equivalence(R=None, Rp=None, u="u", v="v", w="wb"):
    """{R éq., R' éq.} ⊢ (R×R') relation d'équivalence  (II.6.8 ; clos mod. hyp.).

    « S{u,v} est une relation d'équivalence appelée produit de R et R' » (II.6.8) :
    on assemble la symétrie (produit_symetrique) et la transitivité
    (produit_transitive) héritées composante par composante.  La conclusion est
    LITTÉRALEMENT `est_relation_equivalence(R×R')` (symétrie ET transitivité).
    Clos modulo {R sym, R trans, R' sym, R' trans}."""
    if R is None:
        R = E.rel_graphe("GR")
    if Rp is None:
        Rp = E.rel_graphe("GRp")
    sym = produit_symetrique(R, Rp, u, v)
    trans = produit_transitive(R, Rp, u, v, w)
    return conjonction_intro(sym, trans)


# ════════════════════════════════════════════════════════════════════════════
# §6.6 — Relation induite R_A : complément (transitivité, réflexivité)
# ════════════════════════════════════════════════════════════════════════════
# R_A{x,y} := (x∈A et y∈A et R{x,y})  (cf. ensembles_quotient_complements).  La
# symétrie y est déjà prouvée ; on ajoute la transitivité et la réflexivité dans A.

def _relation_induite(R, a):
    """R_A{x,y} := (x∈A et y∈A et R{x,y})  (copie locale de la NOTION II.6.6).

    Identique à `ensembles_quotient_complements.relation_induite` ; recopiée ici
    pour rester strictement dans nos NOUVEAUX fichiers (aucun import croisé requis,
    la notion est purement définitoire)."""
    va = _t(a)

    def rel(x, y):
        return et(et(appartient(x, va), appartient(y, va)), R(x, y))
    return rel


def induite_transitive(R=None, a="A", x="x", y="y", z="z"):
    """{R transitive} ⊢ (∀x)(∀y)(∀z)((R_A{x,y} et R_A{y,z}) ⇒ R_A{x,z})
    (R_A transitive ; II.6.6 ; clos mod. hyp.).

    R_A{x,y} et R_A{y,z} donnent x∈A, z∈A et R{x,y}, R{y,z} ; transitivité de R
    donne R{x,z}, d'où R_A{x,z} = (x∈A et z∈A et R{x,z}).  R à graphe par défaut ;
    A terme ; clos modulo {R transitive}."""
    if R is None:
        R = E.rel_graphe("GR")
    va = _t(a)
    vx, vy, vz = var(x), var(y), var(z)
    RA = _relation_induite(R, va)
    htr = N.assume(E.est_transitive(R, "a", "b", "c"))     # transitivité de R
    h = N.assume(et(RA(vx, vy), RA(vy, vz)))               # R_A{x,y} et R_A{y,z}
    h_xy = conjonction_elim_gauche(h)                      # x∈A et y∈A et R{x,y}
    h_yz = conjonction_elim_droite(h)                      # y∈A et z∈A et R{y,z}
    hx = conjonction_elim_gauche(conjonction_elim_gauche(h_xy))   # x∈A
    hz = conjonction_elim_droite(conjonction_elim_gauche(h_yz))   # z∈A
    rxy = conjonction_elim_droite(h_xy)                    # R{x,y}
    ryz = conjonction_elim_droite(h_yz)                    # R{y,z}
    tr = instancie(instancie(instancie(htr, vx), vy), vz)  # (R{x,y}etR{y,z})⇒R{x,z}
    rxz = N.modus_ponens(conjonction_intro(rxy, ryz), tr)  # R{x,z}
    but = conjonction_intro(conjonction_intro(hx, hz), rxz)   # R_A{x,z}
    imp = N.loi_deduction(et(RA(vx, vy), RA(vy, vz)), but)
    return N.generalisation(x, N.generalisation(y, N.generalisation(z, imp)))


def induite_reflexive_dans(R=None, a="A", e="E", x="x"):
    """{R réflexive dans E, (∀x)(x∈A ⇒ x∈E)} ⊢ (∀x)( R_A{x,x} ⇔ x∈A )
    (R_A réflexive dans A ; II.6.6 ; clos mod. hyp.).

    R_A{x,x} = (x∈A et x∈A et R{x,x}).
    ⇒ : R_A{x,x} donne x∈A (1er conjonct).
    ⇐ : x∈A donne x∈E (par A⊂E) ; R réflexive dans E donne R{x,x} ; on reconstruit
        (x∈A et x∈A et R{x,x}).
    R à graphe par défaut ; A, E termes ; clos modulo {R réflexive dans E, A⊂E}."""
    if R is None:
        R = E.rel_graphe("GR")
    va, ve = _t(a), _t(e)
    vx = var(x)
    RA = _relation_induite(R, va)
    hrefl = N.assume(E.est_reflexive_dans(R, ve, x))   # (∀x)(R{x,x}⇔x∈E)
    hAE = N.assume(pourtout(x, impl(appartient(vx, va), appartient(vx, ve))))  # A⊂E ponctuel
    # ⇒ : R_A{x,x} ⇒ x∈A
    h_fwd = N.assume(RA(vx, vx))
    xinA_fwd = conjonction_elim_gauche(conjonction_elim_gauche(h_fwd))   # x∈A
    imp_fwd = N.loi_deduction(RA(vx, vx), xinA_fwd)     # R_A{x,x} ⇒ x∈A
    # ⇐ : x∈A ⇒ R_A{x,x}
    h_xinA = N.assume(appartient(vx, va))              # x∈A
    xinE = N.modus_ponens(h_xinA, instancie(hAE, vx))  # x∈E
    refl_x = instancie(hrefl, vx)                      # R{x,x} ⇔ x∈E
    from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import equivalence_arriere
    rxx = N.modus_ponens(xinE, equivalence_arriere(refl_x))   # R{x,x}
    RAxx = conjonction_intro(conjonction_intro(h_xinA, h_xinA), rxx)   # R_A{x,x}
    imp_bwd = N.loi_deduction(appartient(vx, va), RAxx)   # x∈A ⇒ R_A{x,x}
    eqv = conjonction_intro(imp_fwd, imp_bwd)          # R_A{x,x} ⇔ x∈A
    return N.generalisation(x, eqv)


def induite_relation_equivalence(R=None, a="A", x="x", y="y", z="z"):
    """{R symétrique, R transitive} ⊢ R_A relation d'équivalence  (II.6.6 ; clos mod. hyp.).

    Assemble la symétrie de R_A (re-prouvée ici depuis la symétrie de R, pour
    rester dans nos fichiers) et la transitivité de R_A (induite_transitive).
    Conclusion LITTÉRALE `est_relation_equivalence(R_A)`.  Clos modulo
    {R symétrique, R transitive}."""
    if R is None:
        R = E.rel_graphe("GR")
    va = _t(a)
    vx, vy = var(x), var(y)
    RA = _relation_induite(R, va)
    # symétrie de R_A
    hsym = N.assume(E.est_symetrique(R, "a", "b"))     # (∀a)(∀b)(R{a,b}⇒R{b,a})
    h = N.assume(RA(vx, vy))                            # x∈A et y∈A et R{x,y}
    appart = conjonction_elim_gauche(h)                # x∈A et y∈A
    hx = conjonction_elim_gauche(appart)               # x∈A
    hy = conjonction_elim_droite(appart)               # y∈A
    rxy = conjonction_elim_droite(h)                   # R{x,y}
    imp_s = instancie(instancie(hsym, vx), vy)         # R{x,y}⇒R{y,x}
    ryx = N.modus_ponens(rxy, imp_s)                   # R{y,x}
    but = conjonction_intro(conjonction_intro(hy, hx), ryx)   # R_A{y,x}
    imp = N.loi_deduction(RA(vx, vy), but)
    sym = N.generalisation(x, N.generalisation(y, imp))
    # transitivité de R_A
    trans = induite_transitive(R, a, x, y, z)
    return conjonction_intro(sym, trans)


# ════════════════════════════════════════════════════════════════════════════
# §6.7 — « plus fine » est un PRÉORDRE sur les relations
# ════════════════════════════════════════════════════════════════════════════
# plus_fine(S, R) := (∀x)(∀y)(S{x,y} ⇒ R{x,y})  (II.6.7).  Réflexive : R plus fine
# que R (R{x,y}⇒R{x,y}).  Transitive : si S plus fine T et T plus fine R, alors S
# plus fine R (composition d'implications).

def plus_fine_reflexive(R=None, x="x", y="y"):
    """⊢ R plus fine que R  (II.6.7 ; INCONDITIONNEL).

    plus_fine(R,R) = (∀x)(∀y)(R{x,y}⇒R{x,y}) : implication identité, généralisée.
    Aucune hypothèse.  R à graphe par défaut."""
    if R is None:
        R = E.rel_graphe("GR")
    vx, vy = var(x), var(y)
    h = N.assume(R(vx, vy))                            # R{x,y}
    imp = N.loi_deduction(R(vx, vy), h)                # R{x,y} ⇒ R{x,y}
    return N.generalisation(x, N.generalisation(y, imp))


def plus_fine_transitive(S=None, T=None, R=None, x="x", y="y"):
    """{S plus fine que T, T plus fine que R} ⊢ S plus fine que R  (II.6.7 ; clos mod. hyp.).

    plus_fine est TRANSITIVE (préordre) : sous S{x,y}, S plus fine T donne T{x,y},
    puis T plus fine R donne R{x,y}.  Généralisation sur x,y.  S, T, R à graphe par
    défaut ; clos modulo {plus_fine(S,T), plus_fine(T,R)}."""
    if S is None:
        S = E.rel_graphe("GS")
    if T is None:
        T = E.rel_graphe("GT")
    if R is None:
        R = E.rel_graphe("GR")
    vx, vy = var(x), var(y)
    hST = N.assume(E.plus_fine(S, T, x, y))            # (∀x)(∀y)(S{x,y}⇒T{x,y})
    hTR = N.assume(E.plus_fine(T, R, x, y))            # (∀x)(∀y)(T{x,y}⇒R{x,y})
    hS = N.assume(S(vx, vy))                            # S{x,y}
    tImp = instancie(instancie(hST, vx), vy)           # S{x,y}⇒T{x,y}
    tXY = N.modus_ponens(hS, tImp)                     # T{x,y}
    rImp = instancie(instancie(hTR, vx), vy)           # T{x,y}⇒R{x,y}
    rXY = N.modus_ponens(tXY, rImp)                    # R{x,y}
    imp = N.loi_deduction(S(vx, vy), rXY)              # S{x,y}⇒R{x,y}
    return N.generalisation(x, N.generalisation(y, imp))


# ════════════════════════════════════════════════════════════════════════════
# §6.4 — Saturation : une partie saturée est close par R
# ════════════════════════════════════════════════════════════════════════════
# est_saturee(A, G, E) := est_compatible(x↦x∈A, rel_graphe(G))
#                       = (∀x)(∀y)((x∈A et (x,y)∈G) ⇒ y∈A)   (II.6.4).
# C'est exactement « A close par R » (la classe de tout x∈A reste dans A).

def saturee_implique_classe_incluse(g="G", a="A", x="x", y="y"):
    """{A saturée pour R} ⊢ (∀x)(∀y)( (x∈A et R{x,y}) ⇒ y∈A )
    (une partie saturée est close par R ; II.6.4 ; clos mod. hyp.).

    `est_saturee(A,G,E)` se déplie exactement en est_compatible(x↦x∈A, rel_graphe G)
    = (∀x)(∀y)((x∈A et (x,y)∈G) ⇒ y∈A).  On l'instancie en (x,y) : c'est
    LITTÉRALEMENT le cœur « A est réunion de classes » de Bourbaki — pour tout x∈A,
    Cl_R(x) ⊂ A.  R{x,y} = (x,y)∈G (rel_graphe).  G : graphe de R ; A, E termes.
    Clos modulo {A saturée pour R}.  (Le paramètre E de est_saturee n'intervient pas
    dans le déplié — est_compatible ne le mentionne pas ; on le prend = A.)"""
    vg, va = _t(g), _t(a)
    vx, vy = var(x), var(y)
    # est_saturee(A, G, E) avec E pris = A (E n'apparaît pas dans le déplié).
    hyp = E.est_saturee(va, vg, va, x=x)               # (∀x)(∀y)((x∈A et (x,y)∈G)⇒y∈A)
    h = N.assume(hyp)
    return instancie(instancie(h, vx), vy)             # (x∈A et (x,y)∈G) ⇒ y∈A


__all__ = [
    # §6.8 — produit de relations d'équivalence
    "relation_produit_couples",
    "produit_symetrique", "produit_transitive", "produit_relation_equivalence",
    # §6.6 — relation induite R_A (transitivité, réflexivité, assemblage)
    "induite_transitive", "induite_reflexive_dans", "induite_relation_equivalence",
    # §6.7 — « plus fine » préordre
    "plus_fine_reflexive", "plus_fine_transitive",
    # §6.4 — saturation
    "saturee_implique_classe_incluse",
]
