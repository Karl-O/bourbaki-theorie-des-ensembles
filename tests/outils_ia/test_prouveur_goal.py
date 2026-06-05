"""Tests V9 — prouveur GOAL-DIRECTED (chaînage arrière, déduction d'abord).

La déduction rend toute la famille R⇒R immédiate (le verrou de `benchmark_ia`).
Chaque résultat reste un `Theoreme` du noyau.

python -m pytest V9/test_prouveur_goal.py -v
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import implication, negation, disjonction
from bourbaki.logique.propositions import A, B, C, D, SIG_PROP
from bourbaki.logique import noyau
from outils_ia import prouveur_goal
from outils_ia.chercheur_ia import prouver_guide


def _p(but, **kw):
    return prouveur_goal.prouver(but, sig=SIG_PROP, noeuds_max=2500, **kw)


def test_implications_via_deduction_immediates():
    # R⇒R pour R variés : résolus par déduction, sans recherche (0 nœud).
    for X in (A, negation(B), disjonction(A, D)):
        th, noeuds = _p(implication(X, X))
        assert th is not None and th.conclusion == implication(X, X) and th.est_clos
        assert noeuds == 0                      # aucune saturation nécessaire


def test_implication_imbriquee():
    # A ⇒ (B ⇒ A) : deux déductions emboîtées.
    but = implication(A, implication(B, A))
    th, _ = _p(but)
    assert th is not None and th.conclusion == but and th.est_clos


def test_resultat_est_un_theoreme_du_noyau():
    th, _ = _p(implication(A, A))
    assert isinstance(th, noyau.Theoreme)


def test_feuilles_via_tactiques():
    # Feuilles débloquées par les macros-tactiques (contraposition, double négation).
    contrap = implication(implication(A, B),
                          implication(negation(B), negation(A)))
    th, _ = _p(contrap)
    assert th is not None and th.conclusion == contrap and th.est_clos

    dn = implication(A, negation(negation(A)))     # A ⇒ ¬¬A
    th, _ = _p(dn)
    assert th is not None and th.conclusion == dn and th.est_clos

    em = disjonction(A, negation(A))               # tiers exclu A ∨ ¬A
    th, _ = _p(em)
    assert th is not None and th.conclusion == em and th.est_clos


def test_couverture_superieure_a_forward_only():
    # Le goal-directed couvre strictement plus que l'ancien forward-only.
    buts = [implication(X, X) for X in (A, negation(B), disjonction(A, D), negation(C))]
    gd = sum(1 for b in buts if _p(b)[0] is not None)
    fo = sum(1 for b in buts
             if prouver_guide(b, sig=SIG_PROP, noeuds_max=2500)[0] is not None)
    assert gd > fo
    assert gd == len(buts)                      # goal-directed les résout tous
