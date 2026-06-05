"""Tests §II.5 — P(X) et produit d'une famille ∏ X_ι.

Chaque test vérifie la conclusion EXACTE (== cible reconstruite) et est_clos.
"""
from formule import (var, egal, et, impl, non, appartient, inclus, pourtout, equiv)
import ensembles_abrege as E
import ensembles_produit_famille as P


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
    vi = var("i")
    return et(et(E.est_fonctionnel(vF), egal(E.dom(vF), vI)),
              pourtout("i", impl(appartient(vi, vI),
                                 appartient(E.valeur(vF, vi), E.valeur_famille(vf, vi)))))


def test_membre_produit_famille():
    thm = P.membre_produit_famille("f", "I", "F")
    vf, vI, vF = var("f"), var("I"), var("F")
    cible = equiv(appartient(vF, E.produit_famille(vf, vI)), _corps_produit(vF, vf, vI))
    assert thm.conclusion == cible
    assert thm.est_clos


def test_produit_fonctionnel():
    thm = P.produit_fonctionnel("f", "I", "F")
    vf, vI, vF = var("f"), var("I"), var("F")
    cible = impl(appartient(vF, E.produit_famille(vf, vI)), E.est_fonctionnel(vF))
    assert thm.conclusion == cible
    assert thm.est_clos


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


def test_axiomes_bien_formes():
    # les deux nouveaux axiomes sont dans la théorie et exploitables via N.axiome
    import noyau_abrege as N
    t = E.theorie_ensembles()
    assert any(ax == E.AXIOME_PARTIES for ax in t.axiomes)
    assert any(ax == E.AXIOME_PRODUIT_FAM for ax in t.axiomes)
    assert N.axiome(t, E.AXIOME_PARTIES).est_clos
    assert N.axiome(t, E.AXIOME_PRODUIT_FAM).est_clos
