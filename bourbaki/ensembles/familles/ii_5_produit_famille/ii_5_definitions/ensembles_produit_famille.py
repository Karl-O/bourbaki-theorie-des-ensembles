"""§II.5 — Ensemble des parties P(X) et produit d'une famille d'ensembles ∏ X_ι.

Termes définis (E.II.5) avec axiomes caractérisants :
  - P(X) := {Y | Y ⊂ X}            (axiome A3, E.II.5.1) ;
  - ∏_{ι∈I} X_ι := { F | F fonctionnel ∧ dom F = I ∧ (∀ι)(ι∈I ⇒ F(ι)∈X_ι) }
                                    (Déf. 1, E.II.5.3).
P(X) est légitimé par l'AXIOME A3 lui-même (existence) + A1 (unicité) ; le produit
par S8 (sélection dans P(I×A)) + A1, comme produit/image/restriction.

Théorèmes CERTIFIÉS par le noyau (instanciation directe + boîte à outils) :
  - membre_parties           ⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X)               [axiome A3 instancié]
  - vide_dans_parties        ⊢ ∅ ∈ P(X)                            [∅ ⊂ X, ex falso]
  - ensemble_dans_parties    ⊢ X ∈ P(X)                            [X ⊂ X réflexif]
  - parties_croissante       ⊢ (X ⊂ X') ⇒ (P(X) ⊂ P(X'))          [§5.1, monotonie A3]
  - membre_produit_famille   ⊢ (F ∈ ∏) ⇔ corps                     [Déf. 1 instanciée]
  - projection_dans_facteur  ⊢ (F ∈ ∏) ⇒ (ι∈I ⇒ pr_ι(F) ∈ X_ι)    [pr_ι : ∏ → X_ι]
  - produit_fonctionnel      ⊢ (F ∈ ∏) ⇒ (F fonctionnel)           [un élément du
                                                                     produit est un
                                                                     graphe fonctionnel]
  - produit_domaine         ⊢ (F ∈ ∏) ⇒ (dom F = I)                [domaine = I]

Les Propositions 1-11 et leurs corollaires (extension canonique f̂ injective/
surjective, currying 𝓕(B×C;A)≅𝓕(C;𝓕(B;A)), Prop. 4 reparamétrage bijectif,
Prop. 5-6 surjectivité de pr_J / prolongement, associativité, distributivité,
commutation produit/intersection, extension aux produits) sont REPORTÉES (cf.
rapport) : elles exigent une infrastructure absente (extension canonique d'une
correspondance, bijections/sections-rétractions, partitions, complémentaire,
∏ de fonctions) ou de très longues preuves multi-étapes nouvelles.
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, egal, et, impl, non, appartient, inclus, pourtout
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege import syllogisme, inclusion_reflexive
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (instancie, equivalence_avant, equivalence_arriere,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, inclusion_transitive)
from bourbaki.logique.i_3_quantifies.tactiques_abrege_quantif import alpha_pour_tout


# ── P(X) : ensemble des parties ───────────────────────────────────────────────
def _inst_parties(x, y):
    """⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PARTIES)
    return instancie(instancie(ax, x), y)


def membre_parties(x="X", y="Y"):
    """⊢ (Y ∈ P(X)) ⇔ (Y ⊂ X).   (axiome A3 instancié, E.II.5.1.)"""
    return _inst_parties(var(x), var(y))


def vide_dans_parties(x="X"):
    """⊢ ∅ ∈ P(X).   (l'ensemble vide est partie de tout ensemble.)"""
    vX, vz = var(x), var("z")
    ax_vide = N.axiome(E.theorie_ensembles(), E.AXIOME_VIDE)          # (∀z)¬(z∈∅)
    nz = instancie(ax_vide, vz)                                      # ¬(z∈∅)
    # ¬(z∈∅) ⇒ (z∈∅ ⇒ z∈X)   (ex falso : S2 sur ¬(z∈∅), puis c'est ¬(z∈∅)∨(z∈X))
    imp = N.modus_ponens(nz, N.s2(non(appartient(vz, E.VIDE)), appartient(vz, vX)))
    vide_sub = N.generalisation("z", imp)                            # ∅ ⊂ X
    return N.modus_ponens(vide_sub, equivalence_arriere(_inst_parties(vX, E.VIDE)))


def ensemble_dans_parties(x="X"):
    """⊢ X ∈ P(X).   (X est partie de lui-même.)"""
    vX = var(x)
    refl = inclusion_reflexive(x)                                    # X ⊂ X
    return N.modus_ponens(refl, equivalence_arriere(_inst_parties(vX, vX)))


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
    """⊢ (F ∈ ∏) ⇔ ( F fonctionnel ∧ dom F = I ∧ (∀i)(i∈I ⇒ F(i)∈X_i) )."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT_FAM)
    return instancie(instancie(instancie(ax, f), i), ff)


def membre_produit_famille(f="f", i="I", ff="F"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇔ ( F fonctionnel ∧ dom F = I ∧ (∀ι)(ι∈I ⇒ F(ι)∈X_ι) ).
       (Déf. 1, E.II.5.3 — caractérisation de l'appartenance au produit.)"""
    return _inst_produit(var(f), var(i), var(ff))


def produit_fonctionnel(f="f", i="I", ff="F"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇒ (F est un graphe fonctionnel).   (élément du produit.)"""
    vf, vI, vF = var(f), var(i), var(ff)
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    fonctionnel = conjonction_elim_gauche(conjonction_elim_gauche(corps))   # F fonctionnel
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), fonctionnel)


def produit_domaine(f="f", i="I", ff="F"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇒ (dom F = I).   (l'ensemble de définition est I.)"""
    vf, vI, vF = var(f), var(i), var(ff)
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    domaine = conjonction_elim_droite(conjonction_elim_gauche(corps))       # dom F = I
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), domaine)


def projection_dans_facteur(f="f", i="I", ff="F", a="a"):
    """⊢ (F ∈ ∏_{ι∈I} X_ι) ⇒ ((α ∈ I) ⇒ (pr_α(F) ∈ X_α)).   (E.II.5.3 : pr_ι : ∏ → X_ι.)

    pr_α(F) = valeur(F, α) = projection_indice(F, α)."""
    vf, vI, vF, va = var(f), var(i), var(ff), var(a)
    h = N.assume(appartient(vF, E.produit_famille(vf, vI)))
    corps = N.modus_ponens(h, equivalence_avant(_inst_produit(vf, vI, vF)))
    forall = conjonction_elim_droite(corps)                # (∀i)(i∈I ⇒ F(i)∈X_i)
    inst = instancie(forall, va)                           # α∈I ⇒ F(α)∈X_α
    return N.loi_deduction(appartient(vF, E.produit_famille(vf, vI)), inst)


__all__ = ["membre_parties", "vide_dans_parties", "ensemble_dans_parties",
           "parties_croissante", "membre_produit_famille",
           "produit_fonctionnel", "produit_domaine", "projection_dans_facteur"]
