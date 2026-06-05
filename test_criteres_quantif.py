"""Tests V9 — C30 général (instanciation, terme quelconque) et C43 (= S6).

python -m pytest V9/test_criteres_quantif.py -v
"""
from __future__ import annotations

from assemblage import (Assemblage, negation, implication, equivalence, egalite,
                        pour_tout, tau_x, substitution_b_x_a)
from propositions import SIG_PROP
import noyau
from tactiques_egalite import (instanciation, instanciation_en_x,
                               reflexivite_terme, c44)

S = SIG_PROP
X = Assemblage(("x",))
Y = Assemblage(("y",))
R = egalite(X, Y)               # (x = y)


def test_c30_general_terme_quelconque():
    # ⊢ (∀x)R ⇒ (T|x)R pour T = y (terme ≠ x)
    t = instanciation(R, Y, "x", S)
    attendu = implication(pour_tout("x", R), substitution_b_x_a(Y, "x", R))
    assert t.conclusion == attendu and t.est_clos


def test_c30_cas_x_coherent():
    # instanciation(R, x, x) doit coïncider avec instanciation_en_x(R, x)
    t1 = instanciation(R, X, "x", S)
    t2 = instanciation_en_x(R, "x", S)
    assert t1.conclusion == t2.conclusion


def test_c43_est_s6():
    # C43 : (T=U) ⇒ ((T|x)R ⇔ (U|x)R) est littéralement le schéma S6.
    T, U = Assemblage(("a",)), Assemblage(("b",))
    Rrel = egalite(X, Assemblage(("c",)))         # R{x} = (x = c)
    th = noyau.s6(T, U, "x", Rrel, S)
    attendu = implication(egalite(T, U),
                          equivalence(substitution_b_x_a(T, "x", Rrel),
                                      substitution_b_x_a(U, "x", Rrel)))
    assert th.conclusion == attendu and th.est_clos


def test_reflexivite_terme_compose():
    # T = τ_z(z = a) : un terme composé ; ⊢ T = T.
    T = tau_x(egalite(Assemblage(("z",)), Assemblage(("a",))), "z")
    t = reflexivite_terme(T, S)
    assert t.conclusion == egalite(T, T) and t.est_clos


def test_c44_substitutivite_termes():
    # V = τ_z(z = w) (terme à trou w) ; ⊢ (a=b) ⇒ (V{a} = V{b}).
    a, b = Assemblage(("a",)), Assemblage(("b",))
    V = tau_x(egalite(Assemblage(("z",)), Assemblage(("w",))), "z")
    t = c44(a, b, V, "w", S)
    attendu = implication(egalite(a, b),
                          egalite(substitution_b_x_a(a, "w", V),
                                  substitution_b_x_a(b, "w", V)))
    assert t.conclusion == attendu and t.est_clos
