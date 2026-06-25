"""§II.4.2 — ASSOCIATIVITÉ de la réunion d'une famille (Prop. 2, 1re formule).

Module NEUF.  Ne MODIFIE AUCUN fichier existant ; réutilise l'infrastructure de
`ensembles_familles_algebre` (`_inst_reunion`) et le PATRON de famille interne de
`ensembles_chap2_props_restantes` (`famille_reparam`/`axiome_valeur_reparam` :
famille définie par un terme + axiome de valeur en THÉORIE SÉPARÉE, jamais ajoutée
à `theorie_ensembles` qui reste à 22 axiomes).

On formalise, VERBATIM, la PARTIE INCONDITIONNELLE de la Proposition 2 (E.II.4.2)
— l'associativité de la réunion sous une partition (sans hypothèse J_λ ≠ ∅) :

    {couverture (a) , domaine (b)} ⊢  ⋃_{λ∈L} X_λ  =  ⋃_{λ∈L}( ⋃_{ι∈J_λ} X_ι ).

L'hypothèse « L = ⋃_λ J_λ » est FIDÈLEMENT scindée en deux clauses (jamais la
conclusion en hypothèse, jamais d'hypothèse parasite) :
    (a) COUVERTURE :  (∀ι)( ι∈L ⇒ (∃λ)(λ∈L et ι∈J_λ) )
    (b) DOMAINE   :  (∀λ)(∀ι)( (λ∈L et ι∈J_λ) ⇒ ι∈L )
chargées par `loi_deduction` sur leur conjonction (a et b).

FAMILLE INTERNE.  G := (λ ↦ ⋃_{ι∈J_λ} X_ι), c.-à-d. G_λ = reunion_famille(X, J_λ)
avec J_λ = valeur_famille(J, λ).  Famille définie par un terme (C54) ; son axiome
de valeur G_λ = ⋃_{ι∈J_λ} X_ι vit dans une théorie dédiée (AUCUN axiome neuf en
théorie principale ; theorie_ensembles() reste à 22).

STRATÉGIE (double inclusion au point z, puis extensionnalité A1) :
  ⊆  d'un témoin (i∈L, z∈X_i), la couverture (a) fournit λ∈L avec i∈J_λ ; alors
     (i∈J_λ et z∈X_i) injecte z dans ⋃_{ι∈J_λ}X_ι = G_λ, et (λ∈L et z∈G_λ) injecte
     z dans ⋃_{λ∈L}G_λ.  (existe_elimination imbriqué + s5 témoin.)
  ⊇  on α-renomme le ∃ externe droit en binder « l » (pour que J_l ne capture pas
     le binder « i » du ∃ interne), puis d'un témoin (l∈L, z∈G_l) on tire
     (∃i)(i∈J_l et z∈X_i) ; le domaine (b) donne i∈L, d'où (i∈L et z∈X_i) injecte
     z dans ⋃_{λ∈L}X_λ.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import (Terme, var, app, egal, et, impl,
                                       appartient, existe, pourtout)
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche as cg, conjonction_elim_droite as cd,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import (
    existe_elimination, alpha_existe)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_1_definitions_algebre.ensembles_familles_algebre import _inst_reunion
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ══════════════════════════════════════════════════════════════════════════════
# FAMILLE INTERNE  G_λ := ⋃_{ι∈J_λ} X_ι   (définie par un terme, C54).
#   PATRON `famille_reparam`/`axiome_valeur_reparam` : valeur en THÉORIE DÉDIÉE,
#   donc theorie_ensembles() reste à 22 axiomes.
# ══════════════════════════════════════════════════════════════════════════════
def famille_assoc(x, j):
    """G := la famille λ ↦ ⋃_{ι∈J_λ} X_ι  (réunion interne sur J_λ)."""
    return app("fam_assoc_reunion", x, j)


def axiome_valeur_assoc(x, j, l="l"):
    """(∀λ)( G_λ = ⋃_{ι∈J_λ} X_ι ).   (C54 ; comme AXIOME_COMPL_FAM/valeur_reparam.)"""
    vl = var(l)
    return pourtout(l, egal(E.valeur_famille(famille_assoc(x, j), vl),
                            E.reunion_famille(x, E.valeur_famille(j, vl))))


def theorie_valeur_assoc(x, j, l="l"):
    """Théorie dédiée : axiome de valeur de G_λ = ⋃_{ι∈J_λ} X_ι (C54)."""
    return N.Theorie("Famille-assoc-reunion", [axiome_valeur_assoc(x, j, l)])


def _val_assoc(x, j, l):
    """⊢ G_λ = ⋃_{ι∈J_λ} X_ι   (instance de la théorie dédiée)."""
    ax = N.axiome(theorie_valeur_assoc(x, j), axiome_valeur_assoc(x, j))
    return instancie(ax, _t(l))


def _membre_eq(t1, t2, eq_thm, z):
    """De ⊢ t1=t2 déduire ⊢ (z∈t1) ⇔ (z∈t2)   (Leibniz via S6)."""
    return N.modus_ponens(eq_thm, N.s6(t1, t2, "w", appartient(_t(z), var("w"))))


# ══════════════════════════════════════════════════════════════════════════════
# Proposition 2, 1re formule — ASSOCIATIVITÉ de la réunion  (E.II.4.2).
#   {couverture (a) , domaine (b)} ⊢ ⋃_{λ∈L} X_λ = ⋃_{λ∈L}( ⋃_{ι∈J_λ} X_ι ).
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §4.2 Prop.2 | E II.24 L.10-23 | PDF p.75
def associativite_reunion_famille(x="X", j="J", l="L"):
    """{(a) couverture , (b) domaine} ⊢ ⋃_{λ∈L} X_λ = ⋃_{λ∈L}(⋃_{ι∈J_λ} X_ι).

    PARTIE INCONDITIONNELLE de la Prop. 2 (E.II.4.2 ; pas de J_λ ≠ ∅ requis).
    Les deux clauses fidèles modélisent « L = ⋃_λ J_λ » :
        (a)  (∀ι)( ι∈L ⇒ (∃λ)(λ∈L et ι∈J_λ) )                       [couverture]
        (b)  (∀λ)(∀ι)( (λ∈L et ι∈J_λ) ⇒ ι∈L )                       [domaine]
    chargées par `loi_deduction` sur leur conjonction (a et b).  Famille interne
    G_λ = ⋃_{ι∈J_λ} X_ι (`famille_assoc`/`_val_assoc`, théorie séparée → 22 ax.)."""
    vx, vj, vL = _t(x), _t(j), _t(l)
    vz, vi, vl = var("z"), var("i"), var("l")
    G = famille_assoc(vx, vj)
    reun_gauche = E.reunion_famille(vx, vL)            # ⋃_{λ∈L} X_λ
    reun_droite = E.reunion_famille(G, vL)             # ⋃_{λ∈L} G_λ

    # ── clauses (a),(b), chargées SÉPARÉMENT (hypothèses = exactement (a) et (b)) ─
    Jl_i = E.valeur_famille(vj, vl)                    # J_l   (indice externe l)
    couverture = pourtout("i", impl(appartient(vi, vL),
        existe("l", et(appartient(vl, vL), appartient(vi, Jl_i)))))
    domaine = pourtout("l", pourtout("i",
        impl(et(appartient(vl, vL), appartient(vi, Jl_i)), appartient(vi, vL))))
    h_couv = N.assume(couverture)
    h_dom = N.assume(domaine)

    # ══════════════════════════════════════════════════════════════════════════
    # ⊆ :  z ∈ ⋃_{λ∈L} X_λ  ⇒  z ∈ ⋃_{λ∈L} G_λ
    # ══════════════════════════════════════════════════════════════════════════
    hG = N.assume(appartient(vz, reun_gauche))
    # (∃i)(i∈L et z∈X_i)
    ex_i = N.modus_ponens(hG, equivalence_avant(_inst_reunion(vx, vL, vz)))
    body_i = et(appartient(vi, vL), appartient(vz, E.valeur_famille(vx, vi)))
    hbi = N.assume(body_i)
    i_in_L = cg(hbi)
    z_in_Xi = cd(hbi)
    # couverture en ι=i : (∃l)(l∈L et i∈J_l)
    ex_l = N.modus_ponens(i_in_L, instancie(h_couv, vi))
    body_l = et(appartient(vl, vL), appartient(vi, E.valeur_famille(vj, vl)))
    hbl = N.assume(body_l)
    l_in_L = cg(hbl)
    i_in_Jl = cd(hbl)
    # (i∈J_l et z∈X_i) ⇒ z∈⋃_{ι∈J_l}X_ι  (témoin ι=i, binder « i » de REUNION_FAM ;
    # J_l a pour variable libre l, donc PAS de capture du binder « i »).
    Jl = E.valeur_famille(vj, vl)
    inner_reun = E.reunion_famille(vx, Jl)
    inner_body = et(appartient(vi, Jl), appartient(vz, E.valeur_famille(vx, vi)))
    ex_inner = N.modus_ponens(conjonction_intro(i_in_Jl, z_in_Xi),
                              N.s5(inner_body, vi, "i"))
    z_in_inner = N.modus_ponens(ex_inner, equivalence_arriere(_inst_reunion(vx, Jl, vz)))
    # z∈⋃_{ι∈J_l}X_ι = z∈G_l
    Gl = E.valeur_famille(G, vl)
    z_in_Gl = N.modus_ponens(z_in_inner,
                             equivalence_arriere(_membre_eq(Gl, inner_reun, _val_assoc(vx, vj, vl), vz)))
    # (l∈L et z∈G_l) ⇒ z∈⋃_{λ∈L}G_λ  (témoin λ=l)
    outer_body_G = et(appartient(vi, vL), appartient(vz, E.valeur_famille(G, vi)))
    ex_outer = N.modus_ponens(conjonction_intro(l_in_L, z_in_Gl),
                              N.s5(outer_body_G, vl, "i"))
    z_in_droite = N.modus_ponens(ex_outer, equivalence_arriere(_inst_reunion(G, vL, vz)))
    # refermer les deux ∃ (eigenvariables l puis i ; conclusion z∈⋃G_λ close en l,i)
    imp_l = existe_elimination(N.loi_deduction(body_l, z_in_droite), "l")
    z_via_i = N.modus_ponens(ex_l, imp_l)
    imp_i = existe_elimination(N.loi_deduction(body_i, z_via_i), "i")
    z_droite = N.modus_ponens(ex_i, imp_i)
    incl_GD = N.generalisation("z", N.loi_deduction(appartient(vz, reun_gauche), z_droite))

    # ══════════════════════════════════════════════════════════════════════════
    # ⊇ :  z ∈ ⋃_{λ∈L} G_λ  ⇒  z ∈ ⋃_{λ∈L} X_λ
    # ══════════════════════════════════════════════════════════════════════════
    hD = N.assume(appartient(vz, reun_droite))
    # (∃i)(i∈L et z∈G_i), puis α-renommage du binder i → l (pour que J_l ne capture
    # pas le binder « i » du ∃ interne de _inst_reunion).
    ex_i_D = N.modus_ponens(hD, equivalence_avant(_inst_reunion(G, vL, vz)))
    body_iD = et(appartient(vi, vL), appartient(vz, E.valeur_famille(G, vi)))
    ex_l_D = N.modus_ponens(ex_i_D, equivalence_avant(alpha_existe("i", "l", body_iD)))
    body_lD = et(appartient(vl, vL), appartient(vz, E.valeur_famille(G, vl)))
    hblD = N.assume(body_lD)
    l_in_L_D = cg(hblD)
    z_in_Gl_D = cd(hblD)
    # z∈G_l = z∈⋃_{ι∈J_l}X_ι, d'où (∃i)(i∈J_l et z∈X_i)
    Gl_D = E.valeur_famille(G, vl)
    Jl_D = E.valeur_famille(vj, vl)
    inner_reun_D = E.reunion_famille(vx, Jl_D)
    z_in_inner_D = N.modus_ponens(z_in_Gl_D,
                                  equivalence_avant(_membre_eq(Gl_D, inner_reun_D, _val_assoc(vx, vj, vl), vz)))
    ex_i_inner = N.modus_ponens(z_in_inner_D, equivalence_avant(_inst_reunion(vx, Jl_D, vz)))
    body_inner_D = et(appartient(vi, Jl_D), appartient(vz, E.valeur_famille(vx, vi)))
    hbiD = N.assume(body_inner_D)
    i_in_Jl_D = cg(hbiD)
    z_in_Xi_D = cd(hbiD)
    # domaine (b) en (λ=l, ι=i) : (l∈L et i∈J_l) ⇒ i∈L
    dom_li = instancie(instancie(h_dom, vl), vi)
    i_in_L_D = N.modus_ponens(conjonction_intro(l_in_L_D, i_in_Jl_D), dom_li)
    # (i∈L et z∈X_i) ⇒ z∈⋃_{λ∈L}X_λ  (témoin λ=i)
    outer_body_X = et(appartient(vi, vL), appartient(vz, E.valeur_famille(vx, vi)))
    ex_outer_X = N.modus_ponens(conjonction_intro(i_in_L_D, z_in_Xi_D),
                                N.s5(outer_body_X, vi, "i"))
    z_in_gauche = N.modus_ponens(ex_outer_X, equivalence_arriere(_inst_reunion(vx, vL, vz)))
    # refermer les deux ∃ (eigenvariables i puis l ; conclusion z∈⋃X_λ close en i,l)
    imp_iD = existe_elimination(N.loi_deduction(body_inner_D, z_in_gauche), "i")
    z_via_l = N.modus_ponens(ex_i_inner, imp_iD)
    imp_lD = existe_elimination(N.loi_deduction(body_lD, z_via_l), "l")
    z_gauche = N.modus_ponens(ex_l_D, imp_lD)
    incl_DG = N.generalisation("z", N.loi_deduction(appartient(vz, reun_droite), z_gauche))

    # ── extensionnalité A1 : double inclusion ⇒ égalité ─────────────────────────
    # Forme OUVERTE : conclusion = l'égalité des deux réunions (la cible verbatim),
    # hypothèses = EXACTEMENT les 2 clauses (a) couverture et (b) domaine.
    return N.modus_ponens(conjonction_intro(incl_GD, incl_DG),
                          extensionnalite_appliquee(reun_gauche, reun_droite))


# cible : l'égalité des deux réunions (X = famille de valeurs, J = famille des J_λ,
# L = ensemble maître d'indices ; G = famille interne λ ↦ ⋃_{ι∈J_λ} X_ι).
def cible(x="X", j="J", l="L"):
    """⊢ ⋃_{λ∈L} X_λ = ⋃_{λ∈L}(⋃_{ι∈J_λ} X_ι)  (conclusion attendue, sans hypothèses)."""
    vx, vj, vL = _t(x), _t(j), _t(l)
    return egal(E.reunion_famille(vx, vL),
                E.reunion_famille(famille_assoc(vx, vj), vL))


__all__ = [
    "famille_assoc", "axiome_valeur_assoc", "theorie_valeur_assoc",
    "associativite_reunion_famille", "cible",
]
