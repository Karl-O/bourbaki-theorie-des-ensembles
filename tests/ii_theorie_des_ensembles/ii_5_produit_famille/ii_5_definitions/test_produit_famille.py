"""Tests §II.5 — P(X) et produit d'une famille ∏ X_ι.

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et est_clos.
"""
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, egal, et, impl, non, appartient, inclus, pourtout, equiv)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_5_produit_famille.ii_5_definitions import ensembles_produit_famille as P


def test_membre_parties():
    thm = P.membre_parties("X", "Y")
    vX, vY = var("X"), var("Y")
    cible = equiv(appartient(vY, E.parties(vX)), inclus(vY, vX))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_vide_dans_parties():
    thm = P.vide_dans_parties("X")
    assert thm.conclusion == appartient(E.VIDE, E.parties(var("X")))
    assert thm.est_clos


def test_ensemble_dans_parties():
    thm = P.ensemble_dans_parties("X")
    vX = var("X")
    assert thm.conclusion == appartient(vX, E.parties(vX))
    assert thm.est_clos


def test_parties_croissante():
    thm = P.parties_croissante("X", "Xp")
    vX, vXp = var("X"), var("Xp")
    cible = impl(inclus(vX, vXp), inclus(E.parties(vX), E.parties(vXp)))
    assert thm.conclusion == cible
    assert thm.est_clos


def _corps_produit(vF, vf, vI):
    """Le corps à QUATRE conjoints de la Déf. 1 (E II.32), RECONSTRUIT À LA MAIN.

    Le conjoint de TÊTE « F ⊂ I × ⋃_{ι∈I} X_ι » est celui du préambule de la Déf. 1 ;
    il a été rétabli le 26 juil. 2026 (cf. l'avertissement sur AXIOME_PRODUIT_FAM).
    C'est CE test qui verrouille la réparation : sans lui, les accesseurs
    continueraient de se construire avec une conclusion silencieusement décalée."""
    vi = var("i")
    return et(et(et(inclus(vF, E.produit(vI, E.reunion_famille(vf, vI))),
                    E.est_fonctionnel(vF)),
                 egal(E.dom(vF), vI)),
              pourtout("i", impl(appartient(vi, vI),
                                 appartient(E.valeur(vF, vi), E.valeur_famille(vf, vi)))))


def test_membre_produit_famille():
    thm = P.membre_produit_famille("f", "I", "F")
    vf, vI, vF = var("f"), var("I"), var("F")
    cible = equiv(appartient(vF, E.produit_famille(vf, vI)), _corps_produit(vF, vf, vI))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_produit_inclus():
    """⊢ (F ∈ ∏) ⇒ (F ⊂ I × ⋃_{ι∈I} X_ι)  — le conjoint de TÊTE (préambule Déf. 1)."""
    thm = P.produit_inclus("f", "I", "F")
    vf, vI, vF = var("f"), var("I"), var("F")
    cible = impl(appartient(vF, E.produit_famille(vf, vI)),
                 inclus(vF, E.produit(vI, E.reunion_famille(vf, vI))))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_produit_fonctionnel():
    """⊢ (F ∈ ∏) ⇒ est_fonctionnel(F).

    ⚠️ DÉRIVE SILENCIEUSE : avec l'ancien adressage (deux `elim_gauche` au lieu de
    `elim_droite(elim_gauche(elim_gauche))`), ce théorème SE CONSTRUIT ENCORE et
    reste CLOS — sa conclusion devient « F∈∏ ⇒ (F ⊂ I×⋃X_ι et fonct F) ».  Aucun
    garde-fou du noyau ne le signale : seule l'égalité EXACTE ci-dessous le fait."""
    thm = P.produit_fonctionnel("f", "I", "F")
    vf, vI, vF = var("f"), var("I"), var("F")
    cible = impl(appartient(vF, E.produit_famille(vf, vI)), E.est_fonctionnel(vF))
    assert thm.conclusion == cible
    assert thm.est_clos
    # et le PIÈGE explicitement : la conclusion n'est PAS la conjonction décalée
    decale = impl(appartient(vF, E.produit_famille(vf, vI)),
                  et(inclus(vF, E.produit(vI, E.reunion_famille(vf, vI))),
                     E.est_fonctionnel(vF)))
    assert thm.conclusion != decale


def test_produit_domaine():
    thm = P.produit_domaine("f", "I", "F")
    vf, vI, vF = var("f"), var("I"), var("F")
    cible = impl(appartient(vF, E.produit_famille(vf, vI)), egal(E.dom(vF), vI))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_projection_dans_facteur():
    thm = P.projection_dans_facteur("f", "I", "F", "a")
    vf, vI, vF, va = var("f"), var("I"), var("F"), var("a")
    cible = impl(appartient(vF, E.produit_famille(vf, vI)),
                 impl(appartient(va, vI),
                      appartient(E.valeur(vF, va), E.valeur_famille(vf, va))))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_produit_graphe_est_clos():
    """🎯 ⊢ (∀F)( F ∈ ∏ ⇒ est_un_graphe(F) ) — CLOS, 0 hypothèse.

    « Les points du produit sont des graphes » était, avant le 26 juil. 2026, une
    HYPOTHÈSE HONNÊTE portée par une demi-douzaine de modules (H2/H3 de iii_3_6,
    les deux est_un_graphe de extensionnalite_produit) — et même RÉFUTABLE pour
    I=∅.  L'axiome réparé la démontre."""
    thm = P.produit_graphe("f", "I", "F")
    vf, vI, vF = var("f"), var("I"), var("F")
    cible = pourtout("F", impl(appartient(vF, E.produit_famille(vf, vI)),
                               E.est_un_graphe(vF)))
    assert thm.conclusion == cible
    assert thm.est_clos and thm.hypotheses == frozenset()


def test_axiomes_bien_formes():
    # les deux nouveaux axiomes sont dans la théorie et exploitables via N.axiome
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
    t = E.theorie_ensembles()
    assert any(ax == E.AXIOME_PARTIES for ax in t.axiomes)
    assert any(ax == E.AXIOME_PRODUIT_FAM for ax in t.axiomes)
    assert N.axiome(t, E.AXIOME_PARTIES).est_clos
    assert N.axiome(t, E.AXIOME_PRODUIT_FAM).est_clos
