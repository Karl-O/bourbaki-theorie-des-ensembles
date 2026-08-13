"""§II.4.2 — ASSOCIATIVITÉ de l'intersection d'une famille (Prop. 2, 2e formule).

Module NEUF.  DUAL universel (∀) de l'associativité de la réunion
(`ensembles_familles_assoc_reunion`, §II.4.1) : on dualise ∃→∀ et et→impl du PATRON.
Ne MODIFIE AUCUN fichier existant ; réutilise l'infrastructure de
`ensembles_familles` (`_inst_reunion`) et le PATRON de famille interne en THÉORIE
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
assumées SÉPARÉMENT : `.hypotheses` vaut EXACTEMENT {(a), (b), (c)} — trois
formules distinctes, PAS la formule unique « (a) et (b) et (c) ».

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

MIGRATION « ⋂ = SÉLECTION dans ⋃ » (2026-07-24) — ce qui a changé, et pourquoi
l'ÉNONCÉ, lui, N'A PAS changé (statut A).
  AXIOME_INTER_FAM ne dit plus « z∈⋂ ⇔ (∀i)(i∈I⇒z∈X_i) » mais
  « z∈⋂ ⇔ ( z∈⋃ et (∀i)(i∈I⇒z∈X_i) ) », l'ancienne forme étant FAUSSE pour I=∅
  (⋂_{ι∈∅} peuplé de TOUT objet ; outils_ia/audit/preuve_incoherence_inter_vide.py).
  D'où deux motifs de casse dans cette preuve :
    • ÉLIMINATION (3 sites) : projeter la conjonction — `_membres_de_inter`, qui
      délègue à `inter_donne_membres` (inconditionnel).  Direction INCHANGÉE.
    • INTRODUCTION (3 sites) : il faut désormais un TÉMOIN d'indice.  Les trois
      témoins existaient déjà dans le contexte, aucune hypothèse n'a été ajoutée :
        – ⋂_{ι∈J_l}X_ι  ← la clause (c) non-vacuité, jusqu'ici chargée de façon
          INERTE, devient une hypothèse réellement CONSOMMÉE (c'est son rôle chez
          Bourbaki : « J_λ ≠ ∅ ») ;
        – ⋂_{λ∈L}G_λ et ⋂_{λ∈L}X_λ  ← l'ANTÉCÉDENT de l'inclusion en cours : un
          « z ∈ ⋂ » livre lui-même (∃i)(i∈L) via ⋂ ⊂ ⋃ (`_indice_depuis_inter`).
          L'hypothèse « L ≠ ∅ » de Bourbaki est donc ici DÉRIVÉE, pas postulée.
  Conclusion : conclusion et hypothèses de `associativite_inter_famille` sont
  strictement les mêmes qu'avant la migration ; le test n'a pas été touché.

GARDE-FOUS : primitives N.* uniquement (aucun Theoreme fabriqué/_CLE) ; theorie_
ensembles() reste à 22 axiomes ; binders frais (i, l, z) ; α-renommage explicite
là où J_l risquerait de capturer le binder « i » de l'axiome ⋂_FAM.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (Terme, var, app, egal, et, impl,
                                       appartient, existe, pourtout)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche as cg, conjonction_elim_droite as cd,
    equivalence_avant, equivalence_arriere, instancie)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_pour_tout)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_familles import _inst_reunion
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import extensionnalite_appliquee
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_selection_ii4 import (
    inter_donne_membres, inter_inclus_reunion)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_intersection_fondation.ensembles_inter_migration_ii4 import (
    caracterisation_inter_famille_non_vide)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ══════════════════════════════════════════════════════════════════════════════
# PONTS vers la Déf. 2 « ⋂ = SÉLECTION dans ⋃ » (migration du 2026-07-24).
#   L'axiome ⋂_FAM a désormais pour membre droit une CONJONCTION
#   ( z∈⋃ et (∀i)(i∈I ⇒ z∈X_i) ) : l'élimination reste gratuite, l'introduction
#   réclame un TÉMOIN d'indice.  Les deux helpers ci-dessous encapsulent
#   exactement ces deux directions, sans changer l'énoncé de la Proposition.
# ══════════════════════════════════════════════════════════════════════════════
def _membres_de_inter(f, i_set, thm_z_in_inter, z):
    """De Γ ⊢ z∈⋂_{ι∈I}X_ι déduire Γ ⊢ (∀i)(i∈I ⇒ z∈X_i).   (ÉLIMINATION, gratuite.)"""
    return N.modus_ponens(thm_z_in_inter,
                          instancie(inter_donne_membres(f, i_set, "z"), _t(z)))


def _indice_depuis_inter(f, i_set, thm_z_in_inter, z):
    """De Γ ⊢ z∈⋂_{ι∈I}X_ι déduire Γ ⊢ (∃i)(i∈I).   (LE témoin d'indice, gratuit.)

    Route : ⋂ ⊂ ⋃ (projection GAUCHE de la sélection, `inter_inclus_reunion`),
    puis (∃i)(i∈I et z∈X_i) ⇒ (∃i)(i∈I) par C-existentiel (S5 + élimination).
    C'est ce lemme qui garde l'énoncé de la Prop. 2 INCHANGÉ : chaque direction de
    la double inclusion part d'un « z ∈ ⋂ », qui FOURNIT lui-même l'indice."""
    vf, vI, vz, vi = _t(f), _t(i_set), _t(z), var("i")
    zU = N.modus_ponens(thm_z_in_inter,
                        instancie(inter_inclus_reunion(vf, vI, "z"), vz))
    ex_body = N.modus_ponens(zU, equivalence_avant(_inst_reunion(vf, vI, vz)))
    body = et(appartient(vi, vI), appartient(vz, E.valeur_famille(vf, vi)))
    hb = N.assume(body)
    ex_i = N.modus_ponens(cg(hb), N.s5(appartient(vi, vI), vi, "i"))
    return N.modus_ponens(ex_body,
                          existe_elimination(N.loi_deduction(body, ex_i), "i"))


def _inter_intro(f, i_set, thm_indice, thm_membres, z):
    """De Γ ⊢ (∃i)(i∈I) et Γ ⊢ (∀i)(i∈I ⇒ z∈X_i) déduire Γ ⊢ z∈⋂_{ι∈I}X_ι.

    INTRODUCTION : c'est la direction qui exige le témoin depuis la migration.
    `caracterisation_inter_famille_non_vide` rend l'ANCIENNE équivalence sous
    l'hypothèse « I ≠ ∅ » que Bourbaki écrit noir sur blanc (E II.22, Déf. 2)."""
    carac = N.modus_ponens(thm_indice,
                           caracterisation_inter_famille_non_vide(f, i_set, "z"))
    return N.modus_ponens(thm_membres, equivalence_arriere(instancie(carac, _t(z))))


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
# @livre Ch.R §4 Prop.- | E.R.19 item 8 ((41) associativité de l'intersection) | PDF p.322
def associativite_inter_famille(x="X", j="J", l="L"):
    """{(a) couverture , (b) domaine , (c) non-vacuité} ⊢
        ⋂_{λ∈L} X_λ = ⋂_{λ∈L}(⋂_{ι∈J_λ} X_ι).

    2e formule de la Prop. 2 (E.II.4.2 ; DUAL ∀ de l'associativité de la réunion).
    Les trois clauses fidèles modélisent « L = ⋃_λ J_λ » avec J_λ ≠ ∅ :
        (a)  (∀ι)( ι∈L ⇒ (∃λ)(λ∈L et ι∈J_λ) )                       [couverture]
        (b)  (∀λ)(∀ι)( (λ∈L et ι∈J_λ) ⇒ ι∈L )                       [domaine]
        (c)  (∀λ)( λ∈L ⇒ (∃ι)(ι∈J_λ) )                              [non-vacuité]
    assumées SÉPARÉMENT (hypothèses = exactement (a), (b), (c)).  Famille interne
    G_λ = ⋂_{ι∈J_λ} X_ι (`famille_assoc_inter`/`_val_assoc_inter`, théorie séparée
    → 22 ax.).

    STATUT après la migration « ⋂ = sélection dans ⋃ » : A — énoncé IDENTIQUE
    (mêmes hypothèses, même conclusion).  Seule la PREUVE change : élimination par
    `_membres_de_inter`, introduction par `_inter_intro` avec un témoin d'indice
    tiré soit de la clause (c) — désormais réellement consommée, elle n'était
    chargée qu'inertement —, soit de l'antécédent lui-même (`_indice_depuis_inter`)."""
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
    # (∀i)(i∈L ⇒ z∈X_i)   [élimination — inchangée par la migration]
    fa_i = _membres_de_inter(vx, vL, hG, vz)
    # (∃i)(i∈L) — extrait de hG lui-même (⋂ ⊂ ⋃) : le témoin d'indice que
    # l'introduction dans ⋂_{λ∈L}G_λ réclame désormais.  AUCUNE hypothèse neuve.
    ex_L = _indice_depuis_inter(vx, vL, hG, vz)
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
    # INTRODUCTION dans ⋂_{ι∈J_l}X_ι : témoin fourni par la clause (c) (J_λ ≠ ∅),
    # qui n'était chargée que de façon INERTE avant la migration et devient ici
    # une hypothèse réellement CONSOMMÉE — c'est exactement l'usage que Bourbaki
    # en fait (« … dont l'ensemble d'indices n'est pas vide », E II.22 Déf. 2).
    ex_Jl = N.modus_ponens(hlL, instancie(h_nonvac, vl))          # (∃i)(i∈J_l)
    z_in_inner = _inter_intro(vx, Jl, ex_Jl, fa_inner, vz)        # z∈⋂_{ι∈J_l}X_ι
    Gl = E.valeur_famille(G, vl)
    z_in_Gl = N.modus_ponens(z_in_inner,
        equivalence_arriere(_membre_eq(Gl, inner_inter, _val_assoc_inter(vx, vj, vl), vz)))
    fa_l_G = N.generalisation("l",
        N.loi_deduction(appartient(vl, vL), z_in_Gl)) # (∀l)(l∈L ⇒ z∈G_l)
    # α-renommage l→i : (∀i)(i∈L ⇒ z∈G_i)  (binder « i » attendu par le corps de la
    # Déf. 2 que consomme `_inter_intro(G, L, …)`)
    body_lG = impl(appartient(vl, vL), appartient(vz, E.valeur_famille(G, vl)))
    fa_i_G = N.modus_ponens(fa_l_G, equivalence_avant(alpha_pour_tout("l", "i", body_lG)))
    z_droite = _inter_intro(G, vL, ex_L, fa_i_G, vz)   # témoin d'indice : ex_L
    incl_GD = N.generalisation("z",
        N.loi_deduction(appartient(vz, inter_gauche), z_droite))

    # ══════════════════════════════════════════════════════════════════════════
    # ⊇ :  z ∈ ⋂_{λ∈L} G_λ  ⇒  z ∈ ⋂_{λ∈L} X_λ
    # ══════════════════════════════════════════════════════════════════════════
    hD = N.assume(appartient(vz, inter_droite))
    fa_i_GD = _membres_de_inter(G, vL, hD, vz)        # (∀i)(i∈L ⇒ z∈G_i)
    ex_L_D = _indice_depuis_inter(G, vL, hD, vz)      # (∃i)(i∈L), extrait de hD
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
    fa_inner_D = _membres_de_inter(vx, Jl_D, z_in_inner_D, vz)   # (∀i)(i∈J_l ⇒ z∈X_i)
    z_Xi_D = N.modus_ponens(i_in_Jl, instancie(fa_inner_D, vi))  # z∈X_i
    # refermer le ∃l (eigenvariable l ; z∈X_i ne dépend pas de l)
    imp_l = existe_elimination(N.loi_deduction(body_l, z_Xi_D), "l")
    z_Xi_via_l = N.modus_ponens(ex_l, imp_l)          # z∈X_i (clos en l)
    fa_i_X = N.generalisation("i",
        N.loi_deduction(appartient(vi, vL), z_Xi_via_l))         # (∀i)(i∈L ⇒ z∈X_i)
    z_gauche = _inter_intro(vx, vL, ex_L_D, fa_i_X, vz)   # témoin d'indice : ex_L_D
    incl_DG = N.generalisation("z",
        N.loi_deduction(appartient(vz, inter_droite), z_gauche))

    # ── extensionnalité A1 : double inclusion ⇒ égalité ─────────────────────────
    # Forme OUVERTE : conclusion = l'égalité des deux intersections (cible verbatim).
    egalite = N.modus_ponens(conjonction_intro(incl_GD, incl_DG),
                             extensionnalite_appliquee(inter_gauche, inter_droite))
    # La clause (c) non-vacuité (J_λ ≠ ∅) n'est PLUS chargée de façon inerte :
    # depuis la migration « ⋂ = sélection dans ⋃ » elle est réellement CONSOMMÉE
    # (introduction dans ⋂_{ι∈J_l}X_ι, direction ⊆).  `egalite` la porte donc déjà.
    assert h_nonvac.conclusion in egalite.hypotheses, "clause (c) doit être consommée"
    return egalite


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
