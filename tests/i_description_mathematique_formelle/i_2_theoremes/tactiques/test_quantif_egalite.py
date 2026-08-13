"""Tests V9 — quantificateurs (∃, ∀, S5) et égalité (=, ⇔, et, S6, S7).

Énoncés vérifiés VERBATIM sur le PDF scanné (PyMuPDF) :
  conjonction  A et B := ¬(¬A ∨ ¬B)            (E.I.29)
  équivalence  A ⇔ B := (A⇒B) et (B⇒A)         (E.I.30)
  (∃x)R := (τx(R)|x)R ; (∀x)R := ¬(∃x)(¬R)      (E.I.32)
  S5 : (T|x)R ⇒ (∃x)R                          (E.I.33)
  S6 : (T=U) ⇒ ((T|x)R ⇔ (U|x)R)               (E.I.38)
  S7 : (∀x)(R⇔S) ⇒ (τx(R)=τx(S))               (E.I.38)

python -m pytest V9/test_quantif_egalite.py -v
"""
from __future__ import annotations
import pytest

from bourbaki.i_description_mathematique_formelle.assemblage import (
    Assemblage, implication, substitution_b_x_a, tau_x,
    conjonction, equivalence, egalite, existe, pour_tout,
)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_app_lecture import depuis_assemblage, vers_assemblage, est_relation, est_terme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau

# Relations / termes concrets.
R = Assemblage(("=", "x", "a"))     # x = a   (relation, x libre)
S = Assemblage(("=", "x", "b"))     # x = b
T = Assemblage(("c",))              # terme : la lettre c
U = Assemblage(("d",))              # terme : la lettre d


# ── Constructeurs bien formés + round-trip ────────────────────────────────────

@pytest.mark.parametrize("asm", [
    conjonction(R, S),
    equivalence(R, S),
    egalite(T, U),
    existe("x", R),
    pour_tout("x", R),
    pour_tout("x", equivalence(R, S)),
])
def test_round_trip_quantif_egalite(asm):
    assert vers_assemblage(depuis_assemblage(asm)) == asm
    assert est_relation(asm)


def test_existe_est_substitution_de_tau():
    # (∃x)R doit littéralement valoir (τx(R)|x)R.
    assert existe("x", R) == substitution_b_x_a(tau_x(R, "x"), "x", R)


def test_pour_tout_est_negation_existe_negation():
    from bourbaki.i_description_mathematique_formelle.assemblage import negation
    assert pour_tout("x", R) == negation(existe("x", negation(R)))


# ── Primitives S5, S6, S7 ─────────────────────────────────────────────────────

def test_s5_axiome():
    th = noyau.s5(R, T, "x")                       # ⊢ (T|x)R ⇒ (∃x)R
    attendu = implication(substitution_b_x_a(T, "x", R), existe("x", R))
    assert th.conclusion == attendu and th.est_clos


def test_s6_axiome():
    th = noyau.s6(T, U, "x", R)                     # ⊢ (T=U) ⇒ ((T|x)R ⇔ (U|x)R)
    equiv = equivalence(substitution_b_x_a(T, "x", R), substitution_b_x_a(U, "x", R))
    attendu = implication(egalite(T, U), equiv)
    assert th.conclusion == attendu and th.est_clos


def test_s7_axiome():
    th = noyau.s7(R, S, "x")                        # ⊢ (∀x)(R⇔S) ⇒ (τxR = τxS)
    attendu = implication(pour_tout("x", equivalence(R, S)),
                          egalite(tau_x(R, "x"), tau_x(S, "x")))
    assert th.conclusion == attendu and th.est_clos


# ── Garde-fous de sorte (le noyau refuse les arguments mal typés) ──────────────

def test_s5_refuse_terme_comme_relation():
    with pytest.raises(ValueError):
        noyau.s5(T, T, "x")          # R = terme « c » : pas une relation


def test_s5_refuse_relation_comme_terme():
    with pytest.raises(ValueError):
        noyau.s5(R, R, "x")          # T = relation « x=a » : pas un terme


def test_s6_refuse_non_terme():
    with pytest.raises(ValueError):
        noyau.s6(R, U, "x", R)       # T = relation : pas un terme


def test_s7_refuse_non_relation():
    with pytest.raises(ValueError):
        noyau.s7(R, T, "x")          # S = terme : pas une relation
