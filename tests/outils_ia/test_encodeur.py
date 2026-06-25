"""Tests V9 — encodage des valeurs pures (assemblages) pour l'IA numérique."""
from __future__ import annotations

from bourbaki.assemblage.assemblage import Assemblage, implication, negation
from outils_ia.ia.encodeur import encoder, traits_paire, TRAITS

A = Assemblage(("=", "a", "b"))


def test_encoder_longueur_fixe():
    v = encoder(A)
    assert len(v) == len(TRAITS)
    assert all(isinstance(x, float) for x in v)


def test_encoder_compte_les_signes():
    v = dict(zip(TRAITS, encoder(implication(A, A))))
    # ¬A∨A : un OU, un NON, deux égalités, 4 lettres
    assert v["nb_OU"] == 1 and v["nb_NON"] == 1
    assert v["nb_egal"] == 2 and v["nb_lettres"] == 4
    assert v["est_relation"] == 1


def test_encoder_terme_vs_relation():
    er = dict(zip(TRAITS, encoder(Assemblage(("a",)))))["est_relation"]
    assert er == 0                                    # lettre = terme
    assert dict(zip(TRAITS, encoder(A)))["est_relation"] == 1   # (a=b) = relation


def test_encoder_impl_reflexive():
    from bourbaki.assemblage.assemblage import implication
    B = Assemblage(("=", "b", "c"))
    assert dict(zip(TRAITS, encoder(implication(A, A))))["impl_reflexive"] == 1
    assert dict(zip(TRAITS, encoder(implication(A, B))))["impl_reflexive"] == 0


def test_traits_paire_concatene():
    p = traits_paire(A, implication(A, A))
    assert len(p) == 2 * len(TRAITS) + 1              # enc(état)+enc(but)+distance
