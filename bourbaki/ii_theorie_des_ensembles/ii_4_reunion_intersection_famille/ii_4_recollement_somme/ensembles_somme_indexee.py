"""§II.4.8 — LA SOMME INDEXÉE ⊔_{ι∈I} X_ι : l'ENCODAGE (P0 du chantier S3).

P0 — FORME DE somme_famille DANS L'ENCODAGE (décision documentée, TOUT en dépend).
`ensembles_abrege.somme_famille(f, i)` est le terme OPAQUE app("somme_fam", f, i)
(docstring : ∑_{ι∈I} X_ι := ⋃_{ι∈I} (X_ι × {ι}), E.II.4.8, Déf. 8) et AUCUN des
22 axiomes de theorie_ensembles() ne caractérise son appartenance — sans axiome
de définition, RIEN n'est démontrable sur ⊔ (« somme_fam » est un symbole libre,
même statut que le mur « fam » documenté en tête de ensembles_factorielle_def2_rec).
On pose donc ICI l'axiome de DÉFINITION de la Déf. 8, dans une THÉORIE DÉDIÉE
(motif sanctionné du projet : theorie_graphe_terme / theorie_exposant /
theorie_applications / theorie_diagonale_cantor / theorie_segment_extremite) :

  AXIOME_SOMME_FAM :
      (∀f)(∀I)(∀z)( z ∈ ⊔(f,I)  ⇔  (∃i)( (i∈I)  et  (z ∈ X_i × {i}) ) )
  où  X_i := valeur_famille(f, i)   et   X_i × {i} est la « copie marquée ».

CHOIX (et leurs raisons) :
  • MEMBERSHIP « réunion des copies marquées » (PAS la forme couples (u,ι)) :
    c'est LITTÉRALEMENT la Déf. 8 (⋃ de la famille des X_ι×{ι}) — le corps est
    AXIOME_REUNION_FAM recomposé sur la famille marquée ; la structure de couple
    des éléments est DÉLÉGUÉE à AXIOME_PRODUIT (déjà dans les 22).  Existence par
    S8 (sélection dans P((⋃_{ι∈I}X_ι) × I)), unicité par A1 — mêmes titres de
    légitimité que REUNION_FAM / PRODUIT_FAM qui, eux, sont DANS les 22.
  • X_i = VALEUR_FAMILLE (pas valeur) : uniformité stricte avec les QUATRE
    axiomes de familles existants (REUNION_FAM, INTER_FAM, COMPL_FAM,
    PRODUIT_FAM).  Le pont fam↔valeur pour une famille CONCRÈTE (graphe_terme)
    reste une HYPOTHÈSE honnête chez le consommateur — précédent documenté :
    HW/HN de T1c (« MUR STRUCTUREL — OPACITÉ DE valeur_famille »).
  • theorie_ensembles() RESTE À 22 AXIOMES (asserté en test) : l'axiome vit dans
    theorie_somme_famille(), jamais ajouté aux 22.  Rien d'autre n'est postulé
    que la LECTURE de la Déf. 8 ; noyau/subst intouchés.

LIANTS : externes f, I, z ; interne ∃« i » (mêmes lettres qu'AXIOME_REUNION_FAM).
Tout consommateur renomme ∃i vers un liant EXOTIQUE (alpha_existe) avant une
∃-élimination, et n'instancie z/I/f qu'à des termes sans « i » libre.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, et, equiv, appartient, existe, pourtout, subst_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, equivalence_arriere, instancie)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


# ── L'axiome de définition de la Déf. 8 (théorie dédiée, cf. docstring) ───────
_SF, _SI, _SZ, _SIDX = var("f"), var("I"), var("z"), var("i")

# @livre Ch.II §4.8 Def.8 | E II.30 L.1-3 | PDF p.81
#   (« On appelle somme de cette famille d'ensembles la réunion de la famille des
#    ensembles X_ι × {ι} (ι∈I) » — l'axiome est la lecture-membership de cette
#    réunion de copies marquées ; S8+A1, théorie dédiée, cf. tête de module.)
AXIOME_SOMME_FAM = pourtout("f", pourtout("I", pourtout("z",
        equiv(appartient(_SZ, E.somme_famille(_SF, _SI)),
              existe("i", et(appartient(_SIDX, _SI),
                             appartient(_SZ, E.produit(E.valeur_famille(_SF, _SIDX),
                                                       E.singleton(_SIDX)))))))))


def theorie_somme_famille():
    """Théorie ne contenant que l'axiome de définition de ⊔ (E.II.4.8, Déf. 8)."""
    return N.Theorie("Somme-famille", [AXIOME_SOMME_FAM])


# @livre Ch.II §4.8 Def.8 | E II.30 L.1-3 | PDF p.81
def membre_somme_famille(fam, i, z):
    """⊢ (z ∈ ⊔(f,I)) ⇔ (∃i)((i∈I) et (z ∈ X_i×{i})).   (fam, i, z : termes.)

    Instance directe de AXIOME_SOMME_FAM ; le liant interne est « i » — les
    termes fournis ne doivent pas contenir « i » libre (liants exotiques !)."""
    ax = N.axiome(theorie_somme_famille(), AXIOME_SOMME_FAM)
    return instancie(instancie(instancie(ax, _t(fam)), _t(i)), _t(z))


# @livre Ch.II §4.8 Def.8 | E II.30 L.1-3 | PDF p.81
def element_marque_dans_somme(fam, i_set, u, i0):
    """{i0 ∈ I, u ∈ X_{i0}} ⊢ (u, i0) ∈ ⊔(f, I).   (l'injection canonique brute.)

    X_{i0} = valeur_famille(f, i0).  u, i0 : noms exotiques ou termes SANS « i »,
    « p », « q » libres (témoins internes du produit).  Témoin i := i0 dans le
    corps de l'axiome ; copie marquée par _couple_dans_produit_t + i0∈{i0}."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_produit.ensembles_produit_commute import (
        _couple_dans_produit_t)
    vfam, vI, vu, vi = _t(fam), _t(i_set), _t(u), _t(i0)
    Xi = E.valeur_famille(vfam, vi)
    hu = N.assume(appartient(vu, Xi))                      # u ∈ X_{i0}
    hi = N.assume(appartient(vi, vI))                      # i0 ∈ I
    i_in_s = N.modus_ponens(N.reflexivite(vi),
        equivalence_arriere(singleton_membre(vi, vi)))     # i0 ∈ {i0}
    cpl = E.couple(vu, vi)
    prod_in = N.modus_ponens(conjonction_intro(hu, i_in_s),
        _couple_dans_produit_t(vu, vi, Xi, E.singleton(vi)))   # (u,i0) ∈ X_{i0}×{i0}
    corps = et(appartient(var("i"), vI),
               appartient(cpl, E.produit(E.valeur_famille(vfam, var("i")),
                                         E.singleton(var("i")))))
    wit = conjonction_intro(hi, prod_in)
    assert wit.conclusion == subst_f(vi, "i", corps), \
        "element_marque_dans_somme : témoin ≠ (i0|i)corps (« i » libre dans u/i0 ?)"
    ex = N.modus_ponens(wit, N.s5(corps, vi, "i"))         # (∃i)corps
    res = N.modus_ponens(ex, equivalence_arriere(membre_somme_famille(vfam, vI, cpl)))
    assert res.conclusion == appartient(cpl, E.somme_famille(vfam, vI)), \
        "element_marque_dans_somme : conclusion ≠ (u,i0)∈⊔"
    return res


__all__ = ["AXIOME_SOMME_FAM", "theorie_somme_famille", "membre_somme_famille",
           "element_marque_dans_somme"]
