"""Tests V9 — couche tactiques (règles dérivées, toutes vérifiées par le noyau).

python -m pytest V9/test_tactiques.py -v

Remarque : A⇒B (atomes distincts) n'est PAS un théorème clos. Pour exercer les
règles d'enchaînement on part donc d'implications *supposées* (`assume`) et on
vérifie la propagation correcte des hypothèses.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import Assemblage, implication, disjonction
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques import tactiques as T

A = Assemblage(("=", "a", "b"))
B = Assemblage(("=", "b", "c"))
C = Assemblage(("=", "c", "d"))


def test_decomposition_implication():
    a, b = T.antecedent_consequent(implication(A, B))
    assert a == A and b == B


def test_affaiblissement_constructif():
    base = noyau.s1(A)                       # ⊢ (A∨A)⇒A
    aff = T.affaiblissement(base, B)         # ⊢ B ⇒ ((A∨A)⇒A)
    assert aff.conclusion == implication(B, base.conclusion)
    assert aff.est_clos


def test_a_implique_a_via_c6():
    t = T.a_implique_a(A)
    assert t.conclusion == implication(A, A) and t.est_clos


def test_syllogisme_propage_hypotheses():
    ab = noyau.assume(implication(A, B))     # (A⇒B) ⊢ (A⇒B)
    bc = noyau.assume(implication(B, C))     # (B⇒C) ⊢ (B⇒C)
    t = T.syllogisme(ab, bc)                 # (A⇒B),(B⇒C) ⊢ (A⇒C)
    assert t.conclusion == implication(A, C)
    assert t.hypotheses == {implication(A, B), implication(B, C)}


def test_distribution_combinateur_s():
    a_bc = noyau.assume(implication(A, implication(B, C)))
    ab = noyau.assume(implication(A, B))
    t = T.distribution(a_bc, ab)             # ... ⊢ A⇒C
    assert t.conclusion == implication(A, C)
    assert t.hypotheses == {implication(A, implication(B, C)), implication(A, B)}


def test_importation_syllogisme_internalise():
    t = T.importation(A, B, C)               # théorème CLOS
    attendu = implication(implication(A, B),
                          implication(implication(B, C), implication(A, C)))
    assert t.conclusion == attendu and t.est_clos


def test_syllogisme_clos_si_premisses_closes():
    # Avec des prémisses closes réelles, le résultat est clos.
    # ⊢ (A∨A)⇒A  (S1) et  ⊢ A⇒(A∨A) (S2) → ⊢ (A∨A)⇒(A∨A) par syllogisme.
    s1 = noyau.s1(A)                         # ⊢ (A∨A)⇒A
    s2 = noyau.s2(A, A)                      # ⊢ A⇒(A∨A)
    # syllogisme attend (X⇒Y),(Y⇒Z) ; ici X=A∨A, Y=A, Z=A∨A
    t = T.syllogisme(s1, s2)                 # ⊢ (A∨A)⇒(A∨A)
    assert t.conclusion == implication(disjonction(A, A), disjonction(A, A))
    assert t.est_clos
