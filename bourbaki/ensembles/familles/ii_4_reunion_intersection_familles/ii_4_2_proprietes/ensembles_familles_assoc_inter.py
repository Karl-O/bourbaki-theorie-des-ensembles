"""§II.4.2 — ASSOCIATIVITÉ de l'intersection d'une famille (Prop. 2, 2e formule).

Module NEUF.  DUAL universel (∀) de l'associativité de la réunion
(`ensembles_familles_assoc_reunion`, §II.4.1) : on dualise ∃→∀ et et→impl du PATRON.
Ne MODIFIE AUCUN fichier existant ; réutilise l'infrastructure de
`ensembles_familles` (`_inst_inter`) et le PATRON de famille interne en THÉORIE
SÉPARÉE (axiome de valeur jamais ajouté à `theorie_ensembles`, qui reste à 22 ax.).

On formalise, VERBATIM, la 2e formule de la Proposition 2 (E.II.4.2) — le DUAL
pour l'INTERSECTION de l'associativité de la réunion (signalée « 1re formule »
dans la docstring du patron réunion) :

    {(a) couverture , (b) domaine , (c) non-vacuité} ⊢
        ⋂_{λ∈L} X_λ  =  ⋂_{λ∈L}( ⋂_{ι∈J_λ} X_ι ).

Bourbaki exige L ≠ ∅ et J_λ ≠ ∅ pour l'intersection ; l'hypothèse « L = ⋃_λ J_λ »
est FIDÈLEMENT scindée en trois clauses (jamais la conclusion en hypothèse, jamais
d'hypothèse parasite) :
    (a) COUVERTURE   :  (∀ι)( ι∈L ⇒ (∃λ)(λ∈L et ι∈J_λ) )
    (b) DOMAINE      :  (∀λ)(∀ι)( (λ∈L et ι∈J_λ) ⇒ ι∈L )
    (c) NON-VACUITÉ  :  (∀λ)( λ∈L ⇒ (∃ι)(ι∈J_λ) )            [incarne J_λ ≠ ∅]
chargées (assumées) sur leur conjonction (a et b et c).

FAMILLE INTERNE.  G := (λ ↦ ⋂_{ι∈J_λ} X_ι), c.-à-d. G_λ = inter_famille(X, J_λ)
avec J_λ = valeur_famille(J, λ).  Famille définie par un terme (C54) ; son axiome
de valeur G_λ = ⋂_{ι∈J_λ} X_ι vit dans une théorie dédiée (AUCUN axiome neuf en
théorie principale ; theorie_ensembles() reste à 22).

STRATÉGIE (miroir universel exact du patron réunion ; double inclusion au point z,
puis extensionnalité A1) :
  ⊆  z∈⋂_{L}X ⇒ (∀i)(i∈L ⇒ z∈X_i) ; pour un binder externe « l » avec l∈L, on
     montre z∈G_l = (∀i)(i∈J_l ⇒ z∈X_i) : d'un ι=i∈J_l, le domaine (b) en (l,i)
     donne i∈L, d'où z∈X_i ; généralisé en (∀i)(i∈J_l⇒z∈X_i) = z∈⋂_{ι∈J_l}X_ι = z∈G_l
     (J_l a pour variable libre l, donc PAS de capture du binder « i » de ⋂_FAM) ;
     généralisé en (∀l)(l∈L⇒z∈G_l), α-renommé l→i pour z∈⋂_{L}G.
  ⊇  z∈⋂_{L}G ⇒ (∀i)(i∈L ⇒ z∈G_i) ; pour un binder externe « i » avec i∈L, la
     couverture (a) en ι=i donne (∃l)(l∈L et i∈J_l) ; d'un témoin l, z∈G_l =
     z∈⋂_{ι∈J_l}X_ι donne (i∈J_l ⇒ z∈X_i), MP i∈J_l → z∈X_i ; généralisé en
     (∀i)(i∈L⇒z∈X_i) = z∈⋂_{L}X.

GARDE-FOUS : primitives N.* uniquement (aucun Theoreme fabriqué/_CLE) ; theorie_
ensembles() reste à 22 axiomes ; binders frais (i, l, z) ; α-renommage explicite
là où J_l risquerait de capturer le binder « i » de l'axiome ⋂_FAM.
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
    existe_elimination, alpha_pour_tout)
from bourbaki.ensembles.familles.ii_4_reunion_intersection_familles.ii_4_1_definitions_algebre.ensembles_familles import _inst_inter
from bourbaki.ensembles.ii_1_axiomes_algebre.ensembles_theoremes import extensionnalite_appliquee


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ══════════════════════════════════════════════════════════════════════════════
# FAMILLE INTERNE  G_λ := ⋂_{ι∈J_λ} X_ι   (définie par un terme, C54).
#   PATRON `famille_assoc`/`axiome_valeur_assoc` (cf. assoc-réunion) : valeur en
#   THÉORIE DÉDIÉE, donc theorie_ensembles() reste à 22 axiomes.
# ══════════════════════════════════════════════════════════════════════════════
def famille_assoc_inter(x, j):
    """G := la famille λ ↦ ⋂_{ι∈J_λ} X_ι  (intersection interne sur J_λ)."""
    return app("fam_assoc_inter", x, j)


def axiome_valeur_assoc_inter(x, j, l="l"):
    """(∀λ)( G_λ = ⋂_{ι∈J_λ} X_ι ).   (C54 ; comme valeur_reparam, en THÉORIE séparée.)"""
    vl = var(l)
    return pourtout(l, egal(E.valeur_famille(famille_assoc_inter(x, j), vl),
                            E.inter_famille(x, E.valeur_famille(j, vl))))


def theorie_valeur_assoc_inter(x, j, l="l"):
    """Théorie dédiée : axiome de valeur de G_λ = ⋂_{ι∈J_λ} X_ι (C54)."""
    return N.Theorie("Famille-assoc-inter", [axiome_valeur_assoc_inter(x, j, l)])


def _val_assoc_inter(x, j, l):
    """⊢ G_λ = ⋂_{ι∈J_λ} X_ι   (instance de la théorie dédiée)."""
    ax = N.axiome(theorie_valeur_assoc_inter(x, j), axiome_valeur_assoc_inter(x, j))
    return instancie(ax, _t(l))


def _membre_eq(t1, t2, eq_thm, z):
    """De ⊢ t1=t2 déduire ⊢ (z∈t1) ⇔ (z∈t2)   (Leibniz via S6)."""
    return N.modus_ponens(eq_thm, N.s6(t1, t2, "w", appartient(_t(z), var("w"))))


# ══════════════════════════════════════════════════════════════════════════════
# Proposition 2, 2e formule — ASSOCIATIVITÉ de l'intersection  (E.II.4.2).
#   {(a) couverture , (b) domaine , (c) non-vacuité} ⊢
#       ⋂_{λ∈L} X_λ = ⋂_{λ∈L}( ⋂_{ι∈J_λ} X_ι ).
# ══════════════════════════════════════════════════════════════════════════════
# @livre Ch.II §4.2 Prop.2 | E II.24 L.10-23 | PDF p.75
def associativite_inter_famille(x="X", j="J", l="L"):
    """{(a) couverture , (b) domaine , (c) non-vacuité} ⊢
        ⋂_{λ∈L} X_λ = ⋂_{λ∈L}(⋂_{ι∈J_λ} X_ι).

    2e formule de la Prop. 2 (E.II.4.2 ; DUAL ∀ de l'associativité de la réunion).
    Les trois clauses fidèles modélisent « L = ⋃_λ J_λ » avec J_λ ≠ ∅ :
        (a)  (∀ι)( ι∈L ⇒ (∃λ)(λ∈L et ι∈J_λ) )                       [couverture]
        (b)  (∀λ)(∀ι)( (λ∈L et ι∈J_λ) ⇒ ι∈L )                       [domaine]
        (c)  (∀λ)( λ∈L ⇒ (∃ι)(ι∈J_λ) )                              [non-vacuité]
    chargées (assumées) sur leur conjonction (a et b et c).  Famille interne
    G_λ = ⋂_{ι∈J_λ} X_ι (`famille_assoc_inter`/`_val_assoc_inter`, théorie séparée
    → 22 ax.)."""
    vx, vj, vL = _t(x), _t(j), _t(l)
    vz, vi, vl = var("z"), var("i"), var("l")
    G = famille_assoc_inter(vx, vj)
    inter_gauche = E.inter_famille(vx, vL)             # ⋂_{λ∈L} X_λ
    inter_droite = E.inter_famille(G, vL)              # ⋂_{λ∈L} G_λ

    # ── clauses (a),(b),(c), chargées SÉPARÉMENT (hyps = exactement (a),(b),(c)) ──
    Jl_l = E.valeur_famille(vj, vl)                    # J_l   (indice externe l)
    couverture = pourtout("i", impl(appartient(vi, vL),
        existe("l", et(appartient(vl, vL), appartient(vi, Jl_l)))))
    domaine = pourtout("l", pourtout("i",
        impl(et(appartient(vl, vL), appartient(vi, Jl_l)), appartient(vi, vL))))
    non_vacuite = pourtout("l", impl(appartient(vl, vL),
        existe("i", appartient(vi, Jl_l))))
    h_couv = N.assume(couverture)
    h_dom = N.assume(domaine)
    h_nonvac = N.assume(non_vacuite)

    # ══════════════════════════════════════════════════════════════════════════
    # ⊆ :  z ∈ ⋂_{λ∈L} X_λ  ⇒  z ∈ ⋂_{λ∈L} G_λ
    # ══════════════════════════════════════════════════════════════════════════
    hG = N.assume(appartient(vz, inter_gauche))
    # (∀i)(i∈L ⇒ z∈X_i)
    fa_i = N.modus_ponens(hG, equivalence_avant(_inst_inter(vx, vL, vz)))
    # but : z∈⋂_{λ∈L}G_λ = (∀i)(i∈L ⇒ z∈G_i).  On construit d'abord (∀l)(l∈L⇒z∈G_l)
    # avec un binder EXTERNE « l » (pour que J_l ne capture pas le binder « i » de
    # l'axiome ⋂_FAM interne), puis on α-renomme l→i.
    hlL = N.assume(appartient(vl, vL))                 # l∈L
    Jl = E.valeur_famille(vj, vl)                      # J_l (variable libre l)
    inner_inter = E.inter_famille(vx, Jl)             # ⋂_{ι∈J_l} X_ι
    # z∈G_l = (∀i)(i∈J_l ⇒ z∈X_i) : soit i∈J_l, le domaine (b) en (l,i) → i∈L.
    hiJl = N.assume(appartient(vi, Jl))               # i∈J_l
    dom_li = instancie(instancie(h_dom, vl), vi)      # (l∈L et i∈J_l) ⇒ i∈L
    i_in_L = N.modus_ponens(conjonction_intro(hlL, hiJl), dom_li)   # i∈L
    z_Xi = N.modus_ponens(i_in_L, instancie(fa_i, vi))             # z∈X_i
    fa_inner = N.generalisation("i",
        N.loi_deduction(appartient(vi, Jl), z_Xi))    # (∀i)(i∈J_l ⇒ z∈X_i)
    z_in_inner = N.modus_ponens(fa_inner,
        equivalence_arriere(_inst_inter(vx, Jl, vz))) # z∈⋂_{ι∈J_l}X_ι
    Gl = E.valeur_famille(G, vl)
    z_in_Gl = N.modus_ponens(z_in_inner,
        equivalence_arriere(_membre_eq(Gl, inner_inter, _val_assoc_inter(vx, vj, vl), vz)))
    fa_l_G = N.generalisation("l",
        N.loi_deduction(appartient(vl, vL), z_in_Gl)) # (∀l)(l∈L ⇒ z∈G_l)
    # α-renommage l→i : (∀i)(i∈L ⇒ z∈G_i)  (binder attendu par _inst_inter(G,L,z))
    body_lG = impl(appartient(vl, vL), appartient(vz, E.valeur_famille(G, vl)))
    fa_i_G = N.modus_ponens(fa_l_G, equivalence_avant(alpha_pour_tout("l", "i", body_lG)))
    z_droite = N.modus_ponens(fa_i_G, equivalence_arriere(_inst_inter(G, vL, vz)))
    incl_GD = N.generalisation("z",
        N.loi_deduction(appartient(vz, inter_gauche), z_droite))

    # ══════════════════════════════════════════════════════════════════════════
    # ⊇ :  z ∈ ⋂_{λ∈L} G_λ  ⇒  z ∈ ⋂_{λ∈L} X_λ
    # ══════════════════════════════════════════════════════════════════════════
    hD = N.assume(appartient(vz, inter_droite))
    fa_i_GD = N.modus_ponens(hD, equivalence_avant(_inst_inter(G, vL, vz)))  # (∀i)(i∈L⇒z∈G_i)
    # but : z∈⋂_{λ∈L}X_λ = (∀i)(i∈L ⇒ z∈X_i).  Soit i∈L.
    hiL = N.assume(appartient(vi, vL))                # i∈L
    # couverture (a) en ι=i : (∃l)(l∈L et i∈J_l)
    ex_l = N.modus_ponens(hiL, instancie(h_couv, vi))
    body_l = et(appartient(vl, vL), appartient(vi, E.valeur_famille(vj, vl)))  # l∈L et i∈J_l
    hbl = N.assume(body_l)
    l_in_L = cg(hbl)                                  # l∈L
    i_in_Jl = cd(hbl)                                 # i∈J_l
    # z∈G_l = z∈⋂_{ι∈J_l}X_ι, d'où (i∈J_l ⇒ z∈X_i) par instanciation de ⋂_FAM
    z_in_Gl_D = N.modus_ponens(l_in_L, instancie(fa_i_GD, vl))   # z∈G_l
    Gl_D = E.valeur_famille(G, vl)
    Jl_D = E.valeur_famille(vj, vl)
    inner_inter_D = E.inter_famille(vx, Jl_D)
    z_in_inner_D = N.modus_ponens(z_in_Gl_D,
        equivalence_avant(_membre_eq(Gl_D, inner_inter_D, _val_assoc_inter(vx, vj, vl), vz)))
    fa_inner_D = N.modus_ponens(z_in_inner_D,
        equivalence_avant(_inst_inter(vx, Jl_D, vz)))            # (∀i)(i∈J_l ⇒ z∈X_i)
    z_Xi_D = N.modus_ponens(i_in_Jl, instancie(fa_inner_D, vi))  # z∈X_i
    # refermer le ∃l (eigenvariable l ; z∈X_i ne dépend pas de l)
    imp_l = existe_elimination(N.loi_deduction(body_l, z_Xi_D), "l")
    z_Xi_via_l = N.modus_ponens(ex_l, imp_l)          # z∈X_i (clos en l)
    fa_i_X = N.generalisation("i",
        N.loi_deduction(appartient(vi, vL), z_Xi_via_l))         # (∀i)(i∈L ⇒ z∈X_i)
    z_gauche = N.modus_ponens(fa_i_X, equivalence_arriere(_inst_inter(vx, vL, vz)))
    incl_DG = N.generalisation("z",
        N.loi_deduction(appartient(vz, inter_droite), z_gauche))

    # ── extensionnalité A1 : double inclusion ⇒ égalité ─────────────────────────
    # Forme OUVERTE : conclusion = l'égalité des deux intersections (cible verbatim).
    egalite = N.modus_ponens(conjonction_intro(incl_GD, incl_DG),
                             extensionnalite_appliquee(inter_gauche, inter_droite))
    # FIDÉLITÉ Bourbaki : charger la clause (c) non-vacuité (J_λ ≠ ∅) en hypothèse
    # de façon INERTE (sound : on prouve `egalite et (c)` puis on projette `egalite`,
    # ce qui laisse (c) parmi les hypothèses, conformément à l'exigence des 3 clauses).
    return cg(conjonction_intro(egalite, h_nonvac))


# cible : l'égalité des deux intersections (X = famille de valeurs, J = famille des
# J_λ, L = ensemble maître d'indices ; G = famille interne λ ↦ ⋂_{ι∈J_λ} X_ι).
def cible(x="X", j="J", l="L"):
    """⊢ ⋂_{λ∈L} X_λ = ⋂_{λ∈L}(⋂_{ι∈J_λ} X_ι)  (conclusion attendue, sans hypothèses)."""
    vx, vj, vL = _t(x), _t(j), _t(l)
    return egal(E.inter_famille(vx, vL),
                E.inter_famille(famille_assoc_inter(vx, vj), vL))


__all__ = [
    "famille_assoc_inter", "axiome_valeur_assoc_inter", "theorie_valeur_assoc_inter",
    "associativite_inter_famille", "cible",
]
