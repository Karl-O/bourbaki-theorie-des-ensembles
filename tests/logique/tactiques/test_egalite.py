"""Tests V9 — propriétés de l'égalité : symétrie (Th2) et transitivité (Th3).

Énoncés vérifiés verbatim sur le PDF (E.I.40) :
  Théorème 2 : (x = y) ⇒ (y = x)
  Théorème 3 : ((x = y) et (y = z)) ⇒ (x = z)

python -m pytest V9/test_egalite.py -v
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import Assemblage, implication, conjonction, equivalence, egalite
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from bourbaki.logique.i_2_criteres_C.tactiques import tactiques_prop as P
from bourbaki.logique.i_4_egalitaires.tactiques_egalite import importation, symetrie, transitivite

A = Assemblage(("=", "a", "b"))
B = Assemblage(("=", "b", "c"))
C = Assemblage(("=", "c", "d"))


def x(n):  # raccourci : terme-lettre
    return Assemblage((n,))


# ── Élimination conjonction / équivalence ─────────────────────────────────────

def test_conjonction_elim():
    conj = P.conjonction_intro(noyau.s1(A), noyau.s2(A, B))   # ⊢ ((A∨A)⇒A) et (A⇒(A∨B))
    g = P.conjonction_elim_gauche(conj)
    d = P.conjonction_elim_droite(conj)
    assert g.conclusion == noyau.s1(A).conclusion and g.est_clos
    assert d.conclusion == noyau.s2(A, B).conclusion and d.est_clos


def test_equivalence_modus():
    eq = P.equivalence_reflexive(A)              # ⊢ A ⇔ A
    av = P.equivalence_avant(eq)                 # ⊢ A ⇒ A
    assert av.conclusion == implication(A, A)


def test_importation():
    # ⊢ A ⇒ (B ⇒ A) via deux déductions, puis importation → ⊢ (A et B) ⇒ A.
    h = noyau.assume(A)                          # {A} ⊢ A
    t1 = noyau.loi_deduction(B, h)               # {A} ⊢ B ⇒ A
    t2 = noyau.loi_deduction(A, t1)              # ⊢ A ⇒ (B ⇒ A)
    imp = importation(t2)                        # ⊢ (A et B) ⇒ A
    assert imp.conclusion == implication(conjonction(A, B), A) and imp.est_clos


# ── Théorèmes 2 et 3 ──────────────────────────────────────────────────────────

def test_symetrie():
    th = symetrie("x", "y")                      # ⊢ (x=y) ⇒ (y=x)
    attendu = implication(egalite(x("x"), x("y")), egalite(x("y"), x("x")))
    assert th.conclusion == attendu and th.est_clos


def test_transitivite():
    th = transitivite("x", "y", "z")             # ⊢ ((x=y) et (y=z)) ⇒ (x=z)
    premisse = conjonction(egalite(x("x"), x("y")), egalite(x("y"), x("z")))
    attendu = implication(premisse, egalite(x("x"), x("z")))
    assert th.conclusion == attendu and th.est_clos


if __name__ == "__main__":
    print("Théorème 2 (symétrie) :", symetrie("x", "y"))
    print("Théorème 3 (transitivité) :", transitivite("x", "y", "z"))
