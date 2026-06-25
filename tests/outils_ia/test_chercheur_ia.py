"""Tests V9 — recherche guidée par l'IA de pertinence (boucle fermée, vérifiée).

L'IA guide, le noyau certifie. On mesure HONNÊTEMENT les nœuds (modus ponens
vérifiés) : IA vs heuristique de distance. On rapporte le chiffre réel.

python -m pytest V9/test_chercheur_ia.py -v
Benchmark :  python V9/test_chercheur_ia.py
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import implication, disjonction
from bourbaki.logique.i_1_termes_relations.propositions import A, B, C, D, SIG_PROP
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from outils_ia.ia.modele import RegressionLogistique
from outils_ia.ia.chercheur_ia import jeu_relevance, prouver_guide
from outils_ia.ia.encodeur import traits_paire_seq

# Buts d'entraînement et de test (fragment propositionnel, atomes).
_ENTRAIN = [implication(A, A), implication(B, B),
            implication(disjonction(A, A), A), implication(A, disjonction(A, B))]
_TEST = [implication(C, C), implication(disjonction(B, B), B)]


def _modele_entraine():
    X, y = jeu_relevance(_ENTRAIN)
    m = RegressionLogistique(len(traits_paire_seq(A, A)))
    m.entrainer(X, y, epochs=200, lr=0.2)
    return m


def test_resultat_verifie():
    th, _ = prouver_guide(implication(A, A))
    assert isinstance(th, noyau.Theoreme)
    assert th.conclusion == implication(A, A) and th.est_clos


def test_guide_par_ia_trouve_et_certifie():
    m = _modele_entraine()
    for but in _TEST:
        th, _ = prouver_guide(but, modele=m)
        assert th is not None and th.conclusion == but and th.est_clos


def test_jeu_relevance_non_vide():
    X, y = jeu_relevance(_ENTRAIN)
    assert len(X) >= 6 and set(y) == {0, 1}


if __name__ == "__main__":
    m = _modele_entraine()
    n_dist = sum(prouver_guide(b)[1] for b in _TEST)
    n_ia = sum(prouver_guide(b, modele=m)[1] for b in _TEST)
    print("Nœuds (modus ponens VÉRIFIÉS) sur les buts de test :")
    print(f"  heuristique de distance : {n_dist}")
    print(f"  IA de pertinence        : {n_ia}")
    if n_dist:
        print(f"  écart réel              : {round(100*(n_dist-n_ia)/n_dist,1)} %")
    print("\nL'IA guide, le noyau certifie : chaque résultat est un Theoreme prouvé.")
