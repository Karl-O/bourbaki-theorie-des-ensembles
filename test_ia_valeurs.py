"""Tests V9 — « ta propre IA » : modèle numérique sur valeurs pures (atomes ∨¬AA).

Étiquettes garanties par le noyau. Évaluation HONNÊTE (jeu de test séparé). Le
modèle reconnaît la *forme* d'un théorème ; il ne décide pas la théorémicité —
le décideur, c'est le noyau.

python -m pytest V9/test_ia_valeurs.py -v
Démo :  python V9/test_ia_valeurs.py
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import implication
from bourbaki.logique.propositions import A, B, C, SIG_PROP
from outils_ia.encodeur import encoder, encoder_sequence, TRAITS
from outils_ia.modele import RegressionLogistique
from outils_ia.donnees_entrainement import jeu_de_donnees

_COMPTES = lambda a: encoder(a, SIG_PROP)          # encodage par comptes (sig atomes)


def _split(X, y):
    """Découpe déterministe : 1 sur 4 en test."""
    Xtr, ytr, Xte, yte = [], [], [], []
    for i, (x, c) in enumerate(zip(X, y)):
        if i % 4 == 0:
            Xte.append(x); yte.append(c)
        else:
            Xtr.append(x); ytr.append(c)
    return Xtr, ytr, Xte, yte


def _precision_test(enc, dim):
    X, y, _, _ = jeu_de_donnees(enc=enc)
    Xtr, ytr, Xte, yte = _split(X, y)
    m = RegressionLogistique(dim)
    m.entrainer(Xtr, ytr)
    return m.precision(Xte, yte)


def test_le_modele_apprend():
    X, y, _, _ = jeu_de_donnees()                  # encodage comptes par défaut
    Xtr, ytr, Xte, yte = _split(X, y)
    m = RegressionLogistique(len(TRAITS))
    m.entrainer(Xtr, ytr)
    base = max(sum(yte), len(yte) - sum(yte)) / len(yte)
    assert m.precision(Xte, yte) > base            # bat la classe majoritaire


def test_distingue_A_implique_A_de_A_implique_B():
    X, y, _, _ = jeu_de_donnees(enc=encoder_sequence)
    m = RegressionLogistique(len(encoder_sequence(A)))
    m.entrainer(X, y)
    # ∨¬AA est un théorème ; ∨¬AB n'en est pas un. La séquence les sépare.
    assert m.proba(encoder_sequence(implication(A, A))) \
        > m.proba(encoder_sequence(implication(A, B)))


def test_encodage_sequence_surpasse_comptes():
    """Lire la séquence (∨¬AA vs ∨¬AB) bat l'agrégation en comptes — mesuré."""
    acc_comptes = _precision_test(_COMPTES, len(TRAITS))
    acc_seq = _precision_test(encoder_sequence, len(encoder_sequence(A)))
    assert acc_seq > acc_comptes + 0.1            # la séquence domine nettement
    assert acc_seq >= 0.80                          # honnête : ~0,85 sur données variées


def test_invariance_par_renommage():
    # A⇒A et C⇒C ont la même forme → même encodage séquentiel.
    assert encoder_sequence(implication(A, A)) == encoder_sequence(implication(C, C))
    # mais A⇒A ≠ A⇒B.
    assert encoder_sequence(implication(A, A)) != encoder_sequence(implication(A, B))


def test_jeu_non_trivial():
    X, y, pos, neg = jeu_de_donnees()
    assert len(pos) >= 10 and len(neg) >= 10
    assert set(y) == {0, 1}


if __name__ == "__main__":
    _, _, pos, neg = jeu_de_donnees()
    print(f"Données (atomes propositionnels) : {len(pos)} théorèmes (+), "
          f"{len(neg)} non-théorèmes (-)\n")
    print(f"{'encodage':28} précision test")
    print(f"{'comptes agrégés':28} {_precision_test(_COMPTES, len(TRAITS)):.3f}")
    print(f"{'séquence bi-grammes':28} "
          f"{_precision_test(encoder_sequence, len(encoder_sequence(A))):.3f}")
    print("\nA⇒A = ∨¬AA, A⇒B = ∨¬AB : seule la lecture de la séquence les sépare.")
    print("Le modèle reconnaît la FORME ; le décideur de théorèmes reste le noyau.")
