"""§II.5.3 (remarque) — A ⊂ ∏_{ι∈I} pr_ι⟨A⟩ : la brique POINTWISE.

Remarque (E.II.5.3) : toute partie A du produit ∏_{ι∈I} X_ι est incluse dans le
produit des images directes de ses projections, A ⊂ ∏_{ι∈I} pr_ι⟨A⟩.

──────────────────────────────────────────────────────────────────────────────
FORME FORMALISÉE : POINTWISE, CLOSE, FIDÈLE                            [POINTWISE]
──────────────────────────────────────────────────────────────────────────────
On livre la BRIQUE ponctuelle de la remarque, déchargée en implication (théorème
CLOS, 0 hypothèse pendante) :

    ⊢ ( A ⊂ ∏(f,I)  ∧  F ∈ A  ∧  α ∈ I )  ⇒  ( pr_α(F) ∈ X_α )

avec X_α = valeur_famille(f, α)  et  pr_α(F) = valeur(F, α).  C'est « la
α-coordonnée d'un élément de A vit dans le facteur X_α » : exactement le contenu
ponctuel de A ⊂ ∏_ι pr_ι⟨A⟩, sans dépendre de la notation image directe pr_α⟨A⟩.

POURQUOI cette forme (et pas la forme GLOBALE close A ⊂ ∏_ι pr_ι⟨A⟩).  La forme
globale exige de modéliser pr_ι⟨A⟩ comme TERME « image directe d'une partie par la
coordonnée pr_ι » PLUS un lemme d'introduction (F∈A ∧ y=pr_ι(F)) ⇒ y∈pr_ι⟨A⟩.
Or :
  • le terme d'image directe présent, E.image(G, X) = G⟨X⟩ (E.II.39, Déf. 3),
    s'applique au graphe G d'UNE correspondance fixe ; la coordonnée pr_ι est une
    FAMILLE de correspondances (variant avec ι) et n'a pas de graphe-terme
    préfabriqué utilisable tel quel ici ;
  • le lemme d'introduction (F∈A ∧ y=pr_ι(F)) ⇒ y∈pr_ι⟨A⟩ N'EXISTE PAS dans le
    dépôt (grep image_directe / membre_image / pr_ι⟨A⟩ : la seule image directe
    est E.image, employée pour l'extension canonique Γ̂, §5.1, pas pour pr_ι⟨A⟩).
Construire cette infrastructure dépasserait le périmètre d'une remarque ; la forme
POINTWISE en est la brique exacte, fidèle et robuste, par les SEULES primitives N.*

Preuve (purement « pointwise », par primitives N.* seules) :
  1. de  A ⊂ ∏(f,I)  (= (∀z)(z∈A ⇒ z∈∏(f,I)))  instanciée en z := F,
     et de l'antécédent  F ∈ A,  par modus ponens :  F ∈ ∏(f,I) ;
  2. `projection_dans_facteur` sur ∏(f,I) :  F∈∏(f,I) ⇒ (α∈I ⇒ pr_α(F)∈X_α) ;
     déchargée par les antécédents  F∈∏(f,I)  et  α∈I  :  pr_α(F) ∈ X_α ;
  3. `loi_deduction` décharge la conjonction des trois antécédents honnêtes en
     une implication CLOSE (est_clos = True).

Les hypothèses sont EXACTEMENT les trois antécédents load-bearing (jamais la
conclusion en hypothèse).  theorie_ensembles() RESTE à 22 axiomes (aucun axiome
neuf ici).
"""
from __future__ import annotations

from bourbaki.logique.i_1_termes_relations.formule import var, et, impl, appartient, inclus
from bourbaki.logique.i_2_criteres_C.noyau import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.familles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_famille import (
    projection_dans_facteur)
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_abrege2 import (
    instancie, conjonction_elim_gauche, conjonction_elim_droite)


def _cible(f="f", i="I", aa="A", ff="F", alpha="alpha"):
    """L'énoncé visé (cible) : conjonction des 3 antécédents honnêtes ⇒ pr_α(F)∈X_α.

    ⊢ ( A ⊂ ∏(f,I) ∧ F∈A ∧ α∈I ) ⇒ ( pr_α(F) ∈ X_α )."""
    vf, vI, vA, vF, valpha = var(f), var(i), var(aa), var(ff), var(alpha)
    prod = E.produit_famille(vf, vI)
    X_alpha = E.valeur_famille(vf, valpha)
    pr_alpha_F = E.valeur(vF, valpha)
    hyp = et(et(inclus(vA, prod), appartient(vF, vA)),
             appartient(valpha, vI))
    return impl(hyp, appartient(pr_alpha_F, X_alpha))


# @livre Ch.II §5.3 Rem.- | E II.32 L.27-31 | PDF p.83
def coordonnee_dans_facteur(f="f", i="I", aa="A", ff="F", alpha="alpha"):
    """⊢ ( A ⊂ ∏(f,I) ∧ F∈A ∧ α∈I ) ⇒ ( pr_α(F) ∈ X_α ).
       (§II.5.3, remarque A ⊂ ∏_ι pr_ι⟨A⟩ : la brique pointwise.)        [POINTWISE]

    « La α-coordonnée d'un élément F d'une partie A du produit vit dans le facteur
    X_α. »  C'est le contenu ponctuel de A ⊂ ∏_ι pr_ι⟨A⟩, sans la notation image
    directe pr_α⟨A⟩ (absente du dépôt).  Voir l'en-tête de module pour le statut et
    le choix de forme."""
    vf, vI, vA, vF, valpha = var(f), var(i), var(aa), var(ff), var(alpha)
    prod = E.produit_famille(vf, vI)                       # ∏_{ι∈I} X_ι

    # Conjonction des 3 antécédents honnêtes (load-bearing), associée à gauche.
    hyp = et(et(inclus(vA, prod), appartient(vF, vA)),
             appartient(valpha, vI))
    h = N.assume(hyp)
    h_incl = conjonction_elim_gauche(conjonction_elim_gauche(h))   # A ⊂ ∏(f,I)
    h_Fmem = conjonction_elim_droite(conjonction_elim_gauche(h))   # F ∈ A
    h_alpha = conjonction_elim_droite(h)                           # α ∈ I

    # 1. A ⊂ ∏(f,I) = (∀z)(z∈A ⇒ z∈∏(f,I)) ; instancier en z := F, décharger F∈A.
    incl_F = instancie(h_incl, vF)                         # F∈A ⇒ F∈∏(f,I)
    F_in_prod = N.modus_ponens(h_Fmem, incl_F)             # F ∈ ∏(f,I)

    # 2. projection sur ∏(f,I) : F∈∏(f,I) ⇒ (α∈I ⇒ pr_α(F)∈X_α) ; décharger.
    pdf = projection_dans_facteur(f, i, ff, alpha)         # (F∈∏) ⇒ (α∈I ⇒ pr_α(F)∈X_α)
    pr_in_X = N.modus_ponens(h_alpha,
                             N.modus_ponens(F_in_prod, pdf))       # pr_α(F) ∈ X_α

    # 3. décharger la conjonction des 3 antécédents honnêtes en implication CLOSE.
    return N.loi_deduction(hyp, pr_in_X)


__all__ = ["coordonnee_dans_facteur", "_cible"]
