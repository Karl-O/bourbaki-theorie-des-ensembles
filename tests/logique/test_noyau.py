"""Tests V9 — couche lecture (round-trip) + noyau (preuve vérifiée de A ⇒ A).

Lancer :  python -m pytest V9/test_noyau.py -v
Ou la démo lisible :  python V9/test_noyau.py
"""
from __future__ import annotations
import pytest

from bourbaki.assemblage.assemblage import (
    Assemblage, concat, disjonction, negation, implication, tau_x,
)
from bourbaki.logique.lecture import (
    depuis_assemblage, vers_assemblage, est_significatif,
    est_relation, est_terme, NonSignificatif,
)
from bourbaki.logique import noyau

# Relation atomique concrète : A = (a = b), assemblage « = a b ».
A = Assemblage(("=", "a", "b"))


# ── Couche 1 : lecture ─────────────────────────────────────────────────────────

def test_atome_est_relation():
    assert est_relation(A)
    assert not est_terme(A)


def test_lettre_est_terme():
    assert est_terme(Assemblage(("a",)))
    assert not est_relation(Assemblage(("a",)))


def test_mal_forme_rejete():
    # « = a » : le signe = (arité 2) manque un terme -> non significatif.
    assert not est_significatif(Assemblage(("=", "a")))
    # « ∨ a b » : OU attend des relations, reçoit des termes (lettres).
    assert not est_relation(Assemblage(("OU", "a", "b")))


@pytest.mark.parametrize("asm", [
    A,
    negation(A),
    disjonction(A, A),
    implication(A, A),
    implication(disjonction(A, A), A),                 # S1
    implication(implication(A, A), disjonction(A, A)),  # imbrication
    tau_x(A, "a"),                                      # terme avec τ + ▢ lié
    tau_x(implication(A, A), "a"),                      # τ sur structure
    # τ imbriqués bien formés : τ_c( = a τ_d(= d c) ) — corps de chaque τ = relation.
    tau_x(
        concat(concat(Assemblage(("=",)), Assemblage(("a",))),
               tau_x(Assemblage(("=", "d", "c")), "d")),
        "c",
    ),
])
def test_round_trip(asm):
    """vers_assemblage ∘ depuis_assemblage = identité (lecture unique fidèle)."""
    assert vers_assemblage(depuis_assemblage(asm)) == asm


def test_carre_libre_rejete():
    # un ▢ sans τ lieur n'est pas significatif.
    assert not est_significatif(Assemblage(("CARRE",)))


# ── Couche 2 : noyau ────────────────────────────────────────────────────────────

def prouver_a_implique_a() -> noyau.Theoreme:
    """Preuve bourbakienne de ⊢ A ⇒ A à partir de S1, S2, S4 et du modus ponens.

    1.  t1 = S1[A]                  : (A∨A) ⇒ A
    2.  t2 = S4[A∨A, A, ¬A]         : ((A∨A)⇒A) ⇒ ((A⇒(A∨A)) ⇒ (A⇒A))
    3.  t3 = MP(t1, t2)             : (A⇒(A∨A)) ⇒ (A⇒A)
    4.  t4 = S2[A, A]               : A ⇒ (A∨A)
    5.  t5 = MP(t4, t3)             : A ⇒ A          ∎
    """
    t1 = noyau.s1(A)
    t2 = noyau.s4(disjonction(A, A), A, negation(A))
    t3 = noyau.modus_ponens(t1, t2)
    t4 = noyau.s2(A, A)
    t5 = noyau.modus_ponens(t4, t3)
    return t5


def test_a_implique_a_verifie():
    t = prouver_a_implique_a()
    assert t.conclusion == implication(A, A)
    assert t.est_clos  # aucune hypothèse résiduelle


def test_theoreme_inforgeable():
    # On ne peut pas fabriquer un Theoreme sans la clé du noyau.
    with pytest.raises(PermissionError):
        noyau.Theoreme(frozenset(), implication(A, A), "faux", object())


def test_mp_refuse_premisses_incoherentes():
    # MP avec une mineure qui n'est pas l'antécédent doit échouer.
    t_impl = noyau.s2(A, A)            # A ⇒ (A∨A) : antécédent = A
    faux_r = noyau.s1(A)              # (A∨A)⇒A  ≠ A
    with pytest.raises(ValueError):
        noyau.modus_ponens(faux_r, t_impl)


def test_schema_refuse_non_relation():
    # S1 appliqué à un terme (lettre) doit être refusé.
    with pytest.raises(ValueError):
        noyau.s1(Assemblage(("a",)))


if __name__ == "__main__":
    print("Round-trip lecture sur A ⇒ A :")
    print("  assemblage :", implication(A, A))
    print("  relue      :", vers_assemblage(depuis_assemblage(implication(A, A))))
    print()
    print("Preuve vérifiée de A ⇒ A (A = « a = b ») :")
    t1 = noyau.s1(A);                              print("  1.", t1)
    t2 = noyau.s4(disjonction(A, A), A, negation(A)); print("  2.", t2)
    t3 = noyau.modus_ponens(t1, t2);               print("  3.", t3)
    t4 = noyau.s2(A, A);                           print("  4.", t4)
    t5 = noyau.modus_ponens(t4, t3);               print("  5.", t5)
    print()
    assert t5.conclusion == implication(A, A) and t5.est_clos
    print("OK : ⊢ A ⇒ A est mécaniquement vérifié.")
