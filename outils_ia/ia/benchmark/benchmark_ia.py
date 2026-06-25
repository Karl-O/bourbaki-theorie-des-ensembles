"""Banc d'essai à plus grande échelle : l'IA de pertinence réduit-elle les nœuds ?

Beaucoup de buts (famille R⇒R pour R variés), split train/test, entraînement sur
les traces des buts d'entraînement, mesure sur les buts de TEST (jamais vus).
On compare les nœuds (modus ponens vérifiés) : IA vs heuristique de distance.
Chiffres réels, agrégés ; chaque preuve reste certifiée par le noyau.

  python V9/benchmark_ia.py
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import implication, negation, disjonction
from bourbaki.logique.i_1_termes_relations.propositions import A, B, C, D, E, SIG_PROP
from outils_ia.ia.modele import RegressionLogistique
from outils_ia.ia.encodeur import traits_paire_seq
from outils_ia.ia.chercheur_ia import jeu_relevance, prouver_guide

_ATOMES = [A, B, C, D, E]


def buts() -> list:
    """Famille R⇒R pour R = atome | ¬atome | (atome ∨ atome) : tous prouvables."""
    formes = list(_ATOMES)
    formes += [negation(a) for a in _ATOMES]
    formes += [disjonction(_ATOMES[i], _ATOMES[j])
               for i in range(len(_ATOMES)) for j in range(i + 1, len(_ATOMES))]
    return [implication(X, X) for X in formes]


def split(g):
    test = [b for i, b in enumerate(g) if i % 3 == 0]
    train = [b for i, b in enumerate(g) if i % 3 != 0]
    return train, test


def lancer(noeuds_max: int = 3000):
    g = buts()
    train, test = split(g)
    X, y = jeu_relevance(train, noeuds_max=noeuds_max)
    modele = RegressionLogistique(len(traits_paire_seq(A, A)))
    modele.entrainer(X, y, epochs=200, lr=0.2)

    n_dist = n_ia = communs = 0
    for but in test:
        td, nd = prouver_guide(but, noeuds_max=noeuds_max)
        ti, ni = prouver_guide(but, modele=modele, noeuds_max=noeuds_max)
        if td is not None and ti is not None:
            communs += 1
            n_dist += nd
            n_ia += ni
    return {"buts_train": len(train), "buts_test": len(test),
            "buts_comptes": communs, "noeuds_distance": n_dist, "noeuds_ia": n_ia}


if __name__ == "__main__":
    r = lancer()
    print(f"Buts : {r['buts_train']} entraînement, {r['buts_test']} test "
          f"({r['buts_comptes']} résolus par les deux)")
    print(f"Nœuds (modus ponens vérifiés) sur le TEST :")
    print(f"  heuristique de distance : {r['noeuds_distance']}")
    print(f"  IA de pertinence        : {r['noeuds_ia']}")
    if r["noeuds_distance"]:
        gain = 100 * (r["noeuds_distance"] - r["noeuds_ia"]) / r["noeuds_distance"]
        print(f"  écart réel              : {gain:.1f} %")
    print("\nButs de test jamais vus à l'entraînement ; chaque preuve certifiée par le noyau.")
