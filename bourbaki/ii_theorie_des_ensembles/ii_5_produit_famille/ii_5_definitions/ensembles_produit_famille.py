"""§II.5 — Ensemble des parties P(X) et produit d'une famille d'ensembles ∏ X_ι.

Termes définis (E.II.5) avec axiomes caractérisants :
  - P(X) := {Y | Y ⊂ X}            (axiome A3, E.II.5.1) ;
  - ∏_{ι∈I} X_ι := { F ∈ 𝔓(I×A) | F fonctionnel ∧ dom F = I ∧ (∀ι)(ι∈I ⇒ F(ι)∈X_ι) }
                                    avec A = ⋃_{ι∈I} X_ι   (Déf. 1, E.II.5.3).
P(X) est légitimé par l'AXIOME A3 lui-même (existence) + A1 (unicité) ; le produit
par S8 (sélection dans P(I×A)) + A1, comme produit/image/restriction — et le
conjoint « F ∈ 𝔓(I×A) » est EXACTEMENT ce que Bourbaki écrit en préambule de la
Déf. 1 pour justifier cette sélection.  Il a été absent de l'encodage jusqu'au
26 juil. 2026 (cf. l'avertissement sur `AXIOME_PRODUIT_FAM`) ; son rétablissement
est un REMPLACEMENT — `theorie_ensembles()` vaut 22 avant comme après.

Théorèmes CERTIFIÉS par le noyau (instanciation directe + boîte à outils) :
  - membre_parties           ⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X)               [axiome A3 instancié]
  - vide_dans_parties        ⊢ ∅ ∈ P(X)                            [∅ ⊂ X, ex falso]
  - ensemble_dans_parties    ⊢ X ∈ P(X)                            [X ⊂ X réflexif]
  - parties_croissante       ⊢ (X ⊂ X') ⇒ (P(X) ⊂ P(X'))          [§5.1, monotonie A3]
  - membre_produit_famille   ⊢ (F ∈ ∏) ⇔ corps                     [Déf. 1 instanciée]
  - produit_inclus           ⊢ (F ∈ ∏) ⇒ (F ⊂ I × ⋃X_ι)           [conjoint de TÊTE]
  - projection_dans_facteur  ⊢ (F ∈ ∏) ⇒ (ι∈I ⇒ pr_ι(F) ∈ X_ι)    [pr_ι : ∏ → X_ι]
  - produit_fonctionnel      ⊢ (F ∈ ∏) ⇒ (F fonctionnel)           [univocité]
  - produit_domaine         ⊢ (F ∈ ∏) ⇒ (dom F = I)                [domaine = I]
  - produit_graphe          ⊢ (∀F)(F ∈ ∏ ⇒ est_un_graphe(F))       [CLOS ; « graphe »
                                                                     du préambule de la
                                                                     Déf. 1, jadis une
                                                                     hypothèse honnête]

Les Propositions 1-11 et leurs corollaires (extension canonique f̂ injective/
surjective, currying 𝓕(B×C;A)≅𝓕(C;𝓕(B;A)), Prop. 4 reparamétrage bijectif,
Prop. 5-6 surjectivité de pr_J / prolongement, associativité, distributivité,
commutation produit/intersection, extension aux produits) sont REPORTÉES (cf.
rapport) : elles exigent une infrastructure absente (extension canonique d'une
correspondance, bijections/sections-rétractions, partitions, complémentaire,
∏ de fonctions) ou de très longues preuves multi-étapes nouvelles.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, egal, et, impl, non, appartient, inclus, pourtout
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import syllogisme, inclusion_reflexive
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (instancie, equivalence_avant, equivalence_arriere,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, inclusion_transitive)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import alpha_pour_tout
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    inclus_produit_est_graphe)


# ── P(X) : ensemble des parties ───────────────────────────────────────────────
def _inst_parties(x, y):
    """⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PARTIES)
    return instancie(instancie(ax, x), y)


# @livre Ch.II §5.1 Ax.3 | E II.30 L.17-21 | PDF p.81
def membre_parties(x="X", y="Y"):
    """⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X).   (axiome A3 instancié, E.II.5.1.)"""
    return _inst_parties(var(x), var(y))


# @livre Ch.II §5.1 Prop.- | E II.30 L.18-21 | PDF p.81
def vide_dans_parties(x="X"):
    """⊢ ∅ ∈ P(X).   (l'ensemble vide est partie de tout ensemble.)"""
    vX, vz = var(x), var("z")
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)          # (∀z)¬(z∈∅)
    nz = instancie(ax_vide, vz)                                      # ¬(z∈∅)
    # ¬(z∈∅) ⇒ (z∈∅ ⇒ z∈X)   (ex falso : S2 sur ¬(z∈∅), puis c'est ¬(z∈∅)∨(z∈X))
    imp = N.modus_ponens(nz, N.s2(non(appartient(vz, E.VIDE)), appartient(vz, vX)))
    vide_sub = N.generalisation("z", imp)                            # ∅ ⊂ X
    return N.modus_ponens(vide_sub, equivalence_arriere(_inst_parties(vX, E.VIDE)))


# @livre Ch.II §5.1 Prop.- | E II.30 L.18-21 | PDF p.81
def ensemble_dans_parties(x="X"):
    """⊢ X ∈ P(X).   (X est partie de lui-même.)"""
    vX = var(x)
    refl = inclusion_reflexive(x)                                    # X ⊂ X
    return N.modus_ponens(refl, equivalence_arriere(_inst_parties(vX, vX)))


# @livre Ch.II §5.1 Prop.- | E II.30 L.22-25 | PDF p.81
def parties_croissante(x="X", xp="Xp"):
    """⊢ (X ⊂ X') ⇒ (P(X) ⊂ P(X')).   (E.II.5.1 : X⊂X' entraîne P(X)⊂P(X').)

    Élément lié « Y » (≠ z, le liant interne de inclusion_transitive), puis
    α-renommage du ∀ externe en « z » pour que la conclusion soit exactement
    inclus(P(X), P(X'))."""
    vX, vXp, vY = var(x), var(xp), var("Y")
    h = N.assume(inclus(vX, vXp))                                    # X ⊂ X'
    # Y∈P(X) ⇒ Y⊂X ⇒ Y⊂X' ⇒ Y∈P(X')
    hY = N.assume(appartient(vY, E.parties(vX)))
    Y_sub_X = N.modus_ponens(hY, equivalence_avant(_inst_parties(vX, vY)))   # Y ⊂ X
    trans = inclusion_transitive("Y", x, xp)                # (Y⊂X et X⊂X') ⇒ Y⊂X'
    Y_sub_Xp = N.modus_ponens(conjonction_intro(Y_sub_X, h), trans)         # Y ⊂ X'
    YinPXp = N.modus_ponens(Y_sub_Xp, equivalence_arriere(_inst_parties(vXp, vY)))
    imp = N.loi_deduction(appartient(vY, E.parties(vX)), YinPXp)            # Y∈P(X) ⇒ Y∈P(X')
    incl_Y = N.generalisation("Y", imp)                     # (∀Y)(Y∈P(X)⇒Y∈P(X'))
    # α-renommer le ∀ externe Y → z pour obtenir exactement inclus(P(X),P(X'))
    membre = impl(appartient(var("Y"), E.parties(vX)), appartient(var("Y"), E.parties(vXp)))
    incl_z = N.modus_ponens(incl_Y, equivalence_avant(alpha_pour_tout("Y", "z", membre)))
    return N.loi_deduction(inclus(vX, vXp), incl_z)


# ── ∏_{ι∈I} X_ι : produit d'une famille ───────────────────────────────────────
def _inst_produit(f, i, ff):
    """⊢ (F ∈ ∏) ⇔ ( F ⊂ I×⋃X_ι ∧ F fonctionnel ∧ dom F = I ∧ (∀i)(i∈I ⇒ F(i)∈X_i) ).

    CHEMINS D'ACCÈS dans le corps (conjonction gauche-associée à QUATRE membres,
    depuis la réparation du 26 juil. 2026) :
        g,g,g  → F ⊂ I × ⋃_{ι∈I} X_ι      (le conjoint du PRÉAMBULE de la Déf. 1)
        g,g,d  → est_fonctionnel(F)
        g,d    → dom F = I                 (INCHANGÉ par la réparation)
        d      → (∀ι)(ι∈I ⇒ F(ι)∈X_ι)      (INCHANGÉ par la réparation)"""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT_FAM)
    return instancie(instancie(instancie(ax, f), i), ff)


# @livre Ch.II §5.3 Def.1 | E II.32 L.10-23 | PDF p.83
def membre_produit_famille(f="f", i="I", ff="F"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇔ ( F ⊂ I×⋃X_ι ∧ F fonctionnel ∧ dom F = I
                              ∧ (∀ι)(ι∈I ⇒ F(ι)∈X_ι) ).
       (Déf. 1, E.II.5.3 — caractérisation de l'appartenance au produit.)"""
    return _inst_produit(var(f), var(i), var(ff))


# @livre Ch.II §5.3 Def.1 | E II.32 L.10-15 | PDF p.83
#   (« F est un élément de 𝔓(I × A) », A = ⋃_{ι∈I} X_ι — préambule de la Déf. 1.)
def produit_inclus(f="f", i="I", ff="F"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇒ (F ⊂ I × ⋃_{ι∈I} X_ι).   (conjoint de TÊTE, Déf. 1.)"""
    vf, vI, vF = var(f), var(i), var(ff)
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    incl = conjonction_elim_gauche(                                        # chemin g,g,g
        conjonction_elim_gauche(conjonction_elim_gauche(corps)))
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), incl)


# @livre Ch.II §5.3 Def.1 | E II.32 L.16-23 | PDF p.83
def produit_fonctionnel(f="f", i="I", ff="F"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇒ (F est un graphe fonctionnel).   (élément du produit.)"""
    vf, vI, vF = var(f), var(i), var(ff)
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    fonctionnel = conjonction_elim_droite(                                 # chemin g,g,d
        conjonction_elim_gauche(conjonction_elim_gauche(corps)))
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), fonctionnel)


# @livre Ch.II §5.3 Def.1 | E II.32 L.16-23 | PDF p.83
def produit_domaine(f="f", i="I", ff="F"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇒ (dom F = I).   (l'ensemble de définition est I.)"""
    vf, vI, vF = var(f), var(i), var(ff)
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    domaine = conjonction_elim_droite(conjonction_elim_gauche(corps))       # dom F = I
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), domaine)


# @livre Ch.II §5.3 Def.1 | E II.32 L.24-26 | PDF p.83
def projection_dans_facteur(f="f", i="I", ff="F", a="a"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇒ ((α ∈ I) ⇒ (pr_α(F) ∈ X_α)).   (E.II.5.3 : pr_ι : ∏ → X_ι.)

    pr_α(F) = valeur(F, α) = projection_indice(F, α)."""
    vf, vI, vF, va = var(f), var(i), var(ff), var(a)
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    forall = conjonction_elim_droite(corps)                # (∀i)(i∈I ⇒ F(i)∈X_i)
    inst = instancie(forall, va)                           # α∈I ⇒ F(α)∈X_α
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), inst)


# @livre Ch.II §5.3 Def.1 | E II.32 L.10-15 | PDF p.83
#   (« F un GRAPHE fonctionnel ayant I pour ensemble de définition » : le mot
#    « graphe » du préambule de la Déf. 1, désormais DÉMONTRÉ et non plus supposé.)
def produit_graphe(f="f", i="I", ff="F"):
    """⊢ (∀F)( F ∈ ∏_{ι∈I} X_ι ⇒ est_un_graphe(F) ).   [CLOS, 0 hypothèse]

    « Les points du produit sont des graphes » — c.-à-d. tout élément de F est un
    couple.  Jusqu'au 26 juil. 2026, ce fait n'était PAS dérivable de l'axiome
    encodé (qui avait perdu le conjoint « F ⊂ I×⋃X_ι ») et devait être porté comme
    HYPOTHÈSE HONNÊTE dans une demi-douzaine de modules (H2/H3 de iii_3_6, les deux
    est_un_graphe de `extensionnalite_produit`…).  Pire : sous l'ancien encodage
    cette hypothèse était RÉFUTABLE pour I=∅ (témoin {∅}), donc tout théorème qui
    la portait y était vacueux.  L'axiome réparé la rend CLOSE : conjoint de tête
    puis `inclus_produit_est_graphe`.

    Le liant du ∀ est « F » (celui passé en `ff`) — les sites qui consomment cet
    énoncé l'instancient au point voulu."""
    vf, vI, vF = var(f), var(i), var(ff)
    incl = produit_inclus(f, i, ff)                        # F∈∏ ⇒ F ⊂ I×⋃X_ι
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    graphe = N.modus_ponens(
        N.modus_ponens(h, incl),
        N.loi_deduction(inclus(vF, E.produit(vI, E.reunion_famille(vf, vI))),
                        inclus_produit_est_graphe(vF, vI, E.reunion_famille(vf, vI))))
    res = N.generalisation(ff, N.loi_deduction(
        appartient(vF, E.produit_famille(vf, vI)), graphe))
    assert res.conclusion == pourtout(ff, impl(
        appartient(vF, E.produit_famille(vf, vI)), E.est_un_graphe(vF))), \
        "produit_graphe : conclusion ≠ (∀F)(F∈∏ ⇒ est_un_graphe F)"
    assert res.est_clos, "produit_graphe : non clos"
    return res


__all__ = ["membre_parties", "vide_dans_parties", "ensemble_dans_parties",
           "parties_croissante", "membre_produit_famille", "produit_inclus",
           "produit_fonctionnel", "produit_domaine", "projection_dans_facteur",
           "produit_graphe"]
