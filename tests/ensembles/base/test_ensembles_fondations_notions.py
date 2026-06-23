"""Tests isolés — INTRODUCTION des notions fondamentales chap. II.3
(correspondance / graphe fonctionnel / fonction / application / Id_A).

On vérifie : (1) que chaque prédicat/terme se CONSTRUIT (formule bien formée,
clôture, dépliage fidèle) ; (2) le lemme direct G(Id_A) ⊂ A×A certifié par le noyau.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, egal, et, appartient, inclus, pourtout,
                                       libres_f, afficher_f)
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.ensembles.ii_3_correspondances import ensembles_fondations_notions as F


_A, _B, _G, _X = var("A"), var("B"), var("G"), var("X")


# ── 1. Correspondance (E.II.3.1, Déf. 1) ──────────────────────────────────────
def test_est_une_correspondance_est_inclusion_dans_produit():
    f = F.est_une_correspondance(_G, _A, _B)
    assert f == inclus(_G, E.produit(_A, _B))


def test_correspondance_est_le_triple():
    assert F.correspondance(_G, _A, _B) == E.couple(E.couple(_G, _A), _B)


# ── 2. Graphe fonctionnel / fonction (E.II.3.4, Déf. 9) ───────────────────────
def test_graphe_fonctionnel_synonyme_de_est_fonctionnel():
    assert F.est_un_graphe_fonctionnel(_G) == E.est_fonctionnel(_G)


def test_est_une_fonction_est_un_graphe_fonctionnel():
    assert F.est_une_fonction(_G) == E.est_fonctionnel(_G)


# ── 3. Application de A dans B (E.II.3.4 + E.II.5.2) ───────────────────────────
def test_est_application_trois_conditions():
    f = F.est_application(_G, _A, _B)
    attendu = et(et(E.est_fonctionnel(_G), egal(E.dom(_G), _A)),
                 inclus(_G, E.produit(_A, _B)))
    assert f == attendu


def test_est_application_clos_sur_A_B_G():
    # F(G,A,B) ne doit avoir que G, A, B comme variables libres.
    f = F.est_application(_G, _A, _B)
    assert libres_f(f) == {"G", "A", "B"}


# ── 4. Application identique Id_A (E.II.3.4) ──────────────────────────────────
def test_application_identique_est_fonction_terme():
    # Id_A = fonction_terme(A, x, A) ; son graphe = graphe_terme(A, x).
    assert F.application_identique(_A) == E.fonction_terme(_A, var("x"), _A, "x")
    assert F.graphe_identite(_A) == E.graphe_terme(_A, var("x"), "x")


def test_graphe_identite_variables_libres():
    # graphe_terme(A, x) = app("graphe_terme", A, x) : x est un ARG libre du terme
    # (le liant C54 est porté par l'axiome, pas par le terme app lui-même).
    g = F.graphe_identite(_A)
    f = appartient(var("w"), g)
    assert libres_f(f) == {"w", "A", "x"}


# ── 5. Lemme direct certifié : G(Id_A) ⊂ A×A ──────────────────────────────────
def test_graphe_identite_inclus_dans_produit_certifie():
    from bourbaki.logique.formule import impl, alpha_egal
    thm = F.application_identique_est_application("A")
    # conclusion : G(Id_A) ⊂ A×A   = (∀w)(w∈G ⇒ w∈A×A).
    vw = var("w")
    G = F.graphe_identite(_A)
    attendu = pourtout("w", impl(appartient(vw, G), appartient(vw, E.produit(_A, _A))))
    assert thm.conclusion == attendu
    # = inclus(G, A×A) à renommage près de la variable liée (inclus emploie « z »).
    assert alpha_egal(thm.conclusion, inclus(G, E.produit(_A, _A)))
    # théorème CLOS (aucune hypothèse résiduelle).
    assert thm.hypotheses == frozenset()


def test_affichage_ne_plante_pas():
    for f in (F.est_une_correspondance(_G, _A, _B),
              F.est_une_fonction(_G),
              F.est_application(_G, _A, _B)):
        s = afficher_f(f)
        assert isinstance(s, str) and s
