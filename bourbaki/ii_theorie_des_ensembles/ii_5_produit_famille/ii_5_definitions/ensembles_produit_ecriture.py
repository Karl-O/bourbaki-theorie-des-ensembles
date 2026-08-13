"""§II.5.3 Déf.1 — LA RECETTE DES SITES « ÉCRITURE » du produit d'une famille.

Depuis la réparation de `AXIOME_PRODUIT_FAM` (26 juil. 2026), le corps de la Déf. 1
a QUATRE conjoints, dont le conjoint de TÊTE « F ⊂ I × ⋃_{ι∈I} X_ι » (préambule de
la Déf. 1, E II.32).  Tout site qui CONSTRUIT une appartenance au produit doit donc
le fournir — et il n'est PAS transportable tel quel d'un produit à l'autre, puisque
la réunion ⋃X_ι change avec la famille.

Ce module encapsule la recette une fois pour toutes.  Un site « écriture » typique
(monotonie, égalité des facteurs, commutation avec ⋂, associativité…) a exactement
cette forme :

    Γ ⊢ F ∈ ∏(f,I)                     (le point vient du produit SOURCE)
    Δ ⊢ (∀ι)(ι∈I ⇒ F(ι) ∈ Y_ι)         (on a re-prouvé les valeurs dans le BUT)
    ─────────────────────────────────────────────────────────────────────────
    Γ∪Δ ⊢ F ∈ ∏(g,I)                   `transporter_dans_produit`

et les trois autres conjoints (est_fonctionnel, dom F = I, et « F est un graphe »
obtenu du conjoint de tête SOURCE) sont récupérés du produit source sans effort.
C'est mécanique : aucun site n'a besoin de connaître les chemins d'accès.

FRONTIÈRE.  Ce module ne fabrique aucun `Theoreme` : il instancie l'axiome par
`N.axiome` et compose par les primitives du noyau.  Il n'importe PAS
`ensembles_produit_famille` (qui, lui, importe `..._graphe_briques`) : il
ré-instancie l'axiome localement, ce qui évite tout cycle.  `theorie_ensembles()`
reste à 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions.ensembles_produit_graphe_briques import (
    inclus_produit_est_graphe, pivot_inclusion_produit, hypothese_valeurs,
)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _dech(thm_premisse, thm_but):
    """Décharge la conclusion de `thm_premisse` de `thm_but`, puis coupe (MP)."""
    return N.modus_ponens(thm_premisse,
                          N.loi_deduction(thm_premisse.conclusion, thm_but))


def instance_membre(fam, i, ff):
    """⊢ (F ∈ ∏(f,I)) ⇔ (F ⊂ I×⋃X_ι ∧ fonct F ∧ dom F = I ∧ (∀ι)(ι∈I ⇒ F(ι)∈X_ι)).

    Instance de `AXIOME_PRODUIT_FAM` acceptant des TERMES (le helper déposé dans
    `ensembles_produit_famille` fait `var(...)`, qui corromprait un terme composé)."""
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_PRODUIT_FAM)
    return instancie(instancie(instancie(ax, _t(fam)), _t(i)), _t(ff))


# @livre Ch.II §5.3 Def.1 | E II.32 L.16-23 | PDF p.83
#   (les quatre conjoints de la Déf. 1, et l'unique endroit du dépôt où leurs
#    chemins d'accès dans la conjonction gauche-associée sont écrits.)
def composants_membre(thm_membre, fam, i, ff):
    """De Γ ⊢ F ∈ ∏(f,I), les QUATRE composants, dans l'ordre du corps :

        ( F ⊂ I×⋃X_ι ,  est_fonctionnel(F) ,  dom F = I ,  (∀ι)(ι∈I ⇒ F(ι)∈X_ι) )

    tous sous les mêmes hypothèses Γ.  C'est le SEUL endroit du dépôt où les
    chemins d'accès (g,g,g / g,g,d / g,d / d) sont écrits : un site qui passe par
    ici ne peut plus dériver silencieusement si l'ordre des conjoints rebouge."""
    vf, vI, vF = _t(fam), _t(i), _t(ff)
    assert thm_membre.conclusion == appartient(vF, E.produit_famille(vf, vI)), \
        "composants_membre : le théorème n'est pas « F ∈ ∏(f,I) » pour ces (F, f, I)"
    corps = N.modus_ponens(thm_membre, equivalence_avant(instance_membre(vf, vI, vF)))
    gg = conjonction_elim_gauche(conjonction_elim_gauche(corps))
    return (conjonction_elim_gauche(gg),                       # F ⊂ I × ⋃X_ι
            conjonction_elim_droite(gg),                       # est_fonctionnel(F)
            conjonction_elim_droite(conjonction_elim_gauche(corps)),   # dom F = I
            conjonction_elim_droite(corps))                    # (∀ι)(ι∈I ⇒ F(ι)∈X_ι)


def graphe_du_point(thm_inclus, ff, i, fam):
    """De Γ ⊢ F ⊂ I×⋃X_ι, rendre Γ ⊢ est_un_graphe(F).   (brique B1.)"""
    vf, vI, vF = _t(fam), _t(i), _t(ff)
    A = E.reunion_famille(vf, vI)
    assert thm_inclus.conclusion == inclus(vF, E.produit(vI, A)), \
        "graphe_du_point : le théorème n'est pas « F ⊂ I × ⋃X_ι »"
    return _dech(thm_inclus, inclus_produit_est_graphe(vF, vI, A))


def conjoint_de_tete(thm_graphe, thm_func, thm_dom, thm_valeurs, ff, fam, i, idx="i"):
    """Γ ⊢ F ⊂ I × ⋃_{ι∈I} X_ι, à partir des quatre théorèmes-prémisses.

    C'est le PIVOT (brique B2), avec ses quatre hypothèses déchargées une à une."""
    res = pivot_inclusion_produit(_t(ff), _t(fam), _t(i), idx)
    for premisse in (thm_graphe, thm_func, thm_dom, thm_valeurs):
        res = _dech(premisse, res)
    return res


def corps_membre(thm_tete, thm_func, thm_dom, thm_valeurs):
    """Le corps à QUATRE conjoints, prêt pour `equivalence_arriere(instance_membre)`."""
    return conjonction_intro(conjonction_intro(conjonction_intro(
        thm_tete, thm_func), thm_dom), thm_valeurs)


# @livre Ch.II §5.3 Def.1 | E II.32 L.10-15 | PDF p.83
#   (le PRÉAMBULE de la Déf. 1 : « on en déduit que, pour tout ι∈I, on a F(ι) ∈ A =
#    ⋃_{ι∈I} X_ι, et par suite que F est un élément de 𝔓(I × A) » — c'est exactement
#    ce que cette recette refait à chaque changement de famille.)
def transporter_dans_produit(thm_membre, thm_valeurs, ff, fam_source, fam_but, i,
                             idx="i"):
    """LA RECETTE.  Γ ⊢ F ∈ ∏(f,I) et Δ ⊢ (∀ι)(ι∈I ⇒ F(ι)∈Y_ι)  ⟹  Γ∪Δ ⊢ F ∈ ∏(g,I).

    Le point F change de produit : on garde de la SOURCE ce qui ne dépend pas de la
    famille (est_fonctionnel, dom F = I, et « F est un graphe », lu du conjoint de
    tête source par B1), et on RECONSTRUIT le conjoint de tête du BUT par le pivot
    B2, la réunion ⋃Y_ι n'étant pas celle de la source.

    `thm_valeurs` doit être exactement (∀ι)(ι∈I ⇒ F(ι) ∈ (fam_but)_ι), liant `idx`
    (celui de l'axiome, « i ») — c'est asserté ici, pas supposé."""
    vF, vf, vg, vI = _t(ff), _t(fam_source), _t(fam_but), _t(i)
    assert thm_valeurs.conclusion == hypothese_valeurs(vg, vI, idx, vF), \
        "transporter_dans_produit : thm_valeurs ≠ (∀ι)(ι∈I ⇒ F(ι) ∈ Y_ι)"
    incl_src, func, dom_eq, _vals_src = composants_membre(thm_membre, vf, vI, vF)
    graphe = graphe_du_point(incl_src, vF, vI, vf)
    tete = conjoint_de_tete(graphe, func, dom_eq, thm_valeurs, vF, vg, vI, idx)
    corps = corps_membre(tete, func, dom_eq, thm_valeurs)
    res = N.modus_ponens(corps, equivalence_arriere(instance_membre(vg, vI, vF)))
    assert res.conclusion == appartient(vF, E.produit_famille(vg, vI)), \
        "transporter_dans_produit : conclusion ≠ F ∈ ∏(g,I)"
    return res


__all__ = ["instance_membre", "composants_membre", "graphe_du_point",
           "conjoint_de_tete", "corps_membre", "transporter_dans_produit"]
