"""Critères quantifiés C34, C35, C38 (sous-ensemble verrouillé de C32–C42).

Issus de la couverture C32–C42 (workflow), re-vérifiés ici par le noyau.
Les autres (C32, C33, C39–C42) restent workflow-vérifiés (lock-in à finir) :
compositions plus longues sur la congruence. C36, C37 = métathéorèmes (exclus).
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import (Assemblage, negation, conjonction, implication,
                        existe, pour_tout)
from bourbaki.logique.lecture import DEFAUT
from bourbaki.logique import noyau
from bourbaki.logique.tactiques.tactiques_prop import conjonction_intro
from bourbaki.logique.tactiques.tactiques_egalite import instanciation_en_x
from bourbaki.logique.congruence_quantif import monotonie_existe, congruence_existe
from bourbaki.logique.criteres import criteres_C as K
from bourbaki.logique.criteres import criteres_C_suite2 as KS2


def c34_pour_tout(r, x, y, sig=DEFAUT):
    """⊢ (∀x)(∀y)R ⇔ (∀y)(∀x)R."""
    def sens(a, b):
        H = pour_tout(a, pour_tout(b, r))
        h = noyau.assume(H, sig)
        hb = noyau.modus_ponens(h, instanciation_en_x(pour_tout(b, r), a, sig), sig)
        hr = noyau.modus_ponens(hb, instanciation_en_x(r, b, sig), sig)
        gba = noyau.generalisation(b, noyau.generalisation(a, hr, sig), sig)
        return noyau.loi_deduction(H, gba, sig)
    return conjonction_intro(sens(x, y), sens(y, x), sig)


def c34_existe(r, x, y, sig=DEFAUT):
    """⊢ (∃x)(∃y)R ⇔ (∃y)(∃x)R.  (quantificateur vacant collapsé syntaxiquement.)"""
    def sens(a, b):
        r_exa = noyau.s5(r, Assemblage((a,)), a, sig)      # ⊢ R ⇒ (∃a)R
        return monotonie_existe(monotonie_existe(r_exa, b, sig), a, sig)
    return conjonction_intro(sens(x, y), sens(y, x), sig)


def c35(a, r, x, sig=DEFAUT):
    """⊢ (∀_A x)R ⇔ (∀x)(A ⇒ R).  ((∀_A x)R := ¬(∃x)(A et ¬R).)"""
    # (A et ¬R) ⇔ ¬(A⇒R)  [c24_et_non]  →  sous (∃x)  →  négation
    cong = congruence_existe(KS2.c24_et_non(a, r, sig), x, sig)
    return K.c23_negation(cong, sig)


def c38_1(a, r, x, sig=DEFAUT):
    """⊢ ¬(∀_A x)R ⇔ (∃_A x)(¬R).  (car ¬(∀_A x)R = ¬¬(∃_A x)¬R, double négation.)"""
    ex_a_notr = existe(x, conjonction(a, negation(r)))     # (∃_A x)¬R
    return K.c24_double_negation(ex_a_notr, sig)


__all__ = ["c34_pour_tout", "c34_existe", "c35", "c38_1"]
