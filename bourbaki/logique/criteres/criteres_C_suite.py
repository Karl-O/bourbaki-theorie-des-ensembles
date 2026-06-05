"""C23–C25, C28 (suite) — équivalences, re-vérifiées par le noyau.

Issus de la couverture Phase B (workflow), re-implémentés ici comme tactiques et
re-vérifiés par le noyau dans test_criteres_C_suite.py. On verrouille le
sous-ensemble aux preuves courtes et sûres ; les équivalences les plus longues
(associativité, distributivité, De Morgan, C25 cas 2) restent workflow-vérifiées,
lock-in à finir (voir couverture.py NOTES).
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import (negation, disjonction, conjonction, implication,
                        equivalence, existe)
from bourbaki.logique.lecture import DEFAUT
from bourbaki.logique import noyau
from bourbaki.logique.tactiques.tactiques import syllogisme, mono_gauche, antecedent_consequent
from bourbaki.logique.tactiques.tactiques_prop import (double_negation_intro, double_negation_elim,
                            conjonction_intro, conjonction_elim_gauche,
                            conjonction_elim_droite, equivalence_avant,
                            equivalence_arriere, projection_gauche)
from bourbaki.logique.criteres import criteres_C as K


# ── C23 : congruence de l'équivalence (sous l'hypothèse A⇔B) ──────────────────

def _ab_ba(thm_eq, sig):
    return equivalence_avant(thm_eq, sig), equivalence_arriere(thm_eq, sig)


def c23_impl_droite(thm_eq, c, sig=DEFAUT):
    """{A⇔B} ⊢ (A⇒C) ⇔ (B⇒C)."""
    ab, ba = _ab_ba(thm_eq, sig)
    a, b = antecedent_consequent(ab.conclusion, sig)
    hac = noyau.assume(implication(a, c), sig)
    av = noyau.loi_deduction(implication(a, c), syllogisme(ba, hac, sig), sig)
    hbc = noyau.assume(implication(b, c), sig)
    ar = noyau.loi_deduction(implication(b, c), syllogisme(ab, hbc, sig), sig)
    return conjonction_intro(av, ar, sig)


def c23_impl_gauche(thm_eq, c, sig=DEFAUT):
    """{A⇔B} ⊢ (C⇒A) ⇔ (C⇒B)."""
    ab, ba = _ab_ba(thm_eq, sig)
    a, b = antecedent_consequent(ab.conclusion, sig)
    hca = noyau.assume(implication(c, a), sig)
    av = noyau.loi_deduction(implication(c, a), syllogisme(hca, ab, sig), sig)
    hcb = noyau.assume(implication(c, b), sig)
    ar = noyau.loi_deduction(implication(c, b), syllogisme(hcb, ba, sig), sig)
    return conjonction_intro(av, ar, sig)


def c23_et(thm_eq, c, sig=DEFAUT):
    """{A⇔B} ⊢ (A et C) ⇔ (B et C)."""
    ab, ba = _ab_ba(thm_eq, sig)
    a, b = antecedent_consequent(ab.conclusion, sig)

    def sens(g_impl, x, y):           # (x et C) ⇒ (y et C)
        h = noyau.assume(conjonction(x, c), sig)
        yy = noyau.modus_ponens(conjonction_elim_gauche(h, sig), g_impl, sig)
        cc = conjonction_elim_droite(h, sig)
        return noyau.loi_deduction(conjonction(x, c), conjonction_intro(yy, cc, sig), sig)
    return conjonction_intro(sens(ab, a, b), sens(ba, b, a), sig)


def c23_ou(thm_eq, c, sig=DEFAUT):
    """{A⇔B} ⊢ (A ou C) ⇔ (B ou C)."""
    ab, ba = _ab_ba(thm_eq, sig)
    return conjonction_intro(mono_gauche(ab, c, sig), mono_gauche(ba, c, sig), sig)


# ── C24 : équivalences classiques (closes) ────────────────────────────────────

def c24_contraposition(a, b, sig=DEFAUT):
    """⊢ (A⇒B) ⇔ ((¬B)⇒(¬A))."""
    return conjonction_intro(K.c12(a, b, sig), K.c17(a, b, sig), sig)


def c24_idem_et(a, sig=DEFAUT):
    """⊢ (A et A) ⇔ A."""
    av = projection_gauche(a, a, sig)
    h = noyau.assume(a, sig)
    ar = noyau.loi_deduction(a, conjonction_intro(h, h, sig), sig)
    return conjonction_intro(av, ar, sig)


def c24_idem_ou(a, sig=DEFAUT):
    """⊢ (A ou A) ⇔ A."""
    return conjonction_intro(noyau.s1(a, sig), noyau.s2(a, a, sig), sig)


def c24_comm_et(a, b, sig=DEFAUT):
    """⊢ (A et B) ⇔ (B et A)."""
    def sens(x, y):
        h = noyau.assume(conjonction(x, y), sig)
        swap = conjonction_intro(conjonction_elim_droite(h, sig),
                                 conjonction_elim_gauche(h, sig), sig)
        return noyau.loi_deduction(conjonction(x, y), swap, sig)
    return conjonction_intro(sens(a, b), sens(b, a), sig)


def c24_comm_ou(a, b, sig=DEFAUT):
    """⊢ (A ou B) ⇔ (B ou A)."""
    return conjonction_intro(noyau.s3(a, b, sig), noyau.s3(b, a, sig), sig)


def c24_ou_implique(a, b, sig=DEFAUT):
    """⊢ (A ou B) ⇔ ((¬A) ⇒ B)."""
    av = mono_gauche(double_negation_intro(a, sig), b, sig)   # (A∨B)⇒(¬¬A∨B)
    ar = mono_gauche(double_negation_elim(a, sig), b, sig)    # (¬¬A∨B)⇒(A∨B)
    return conjonction_intro(av, ar, sig)


# ── C28 : ¬(∀x)R ⇔ (∃x)(¬R) ───────────────────────────────────────────────────

def c28(r, x="x", sig=DEFAUT):
    """⊢ ¬(∀x)R ⇔ (∃x)(¬R).  (car ¬(∀x)R EST ¬¬(∃x)¬R ; double négation.)"""
    return K.c24_double_negation(existe(x, negation(r)), sig)


__all__ = ["c23_impl_droite", "c23_impl_gauche", "c23_et", "c23_ou",
           "c24_contraposition", "c24_idem_et", "c24_idem_ou", "c24_comm_et",
           "c24_comm_ou", "c24_ou_implique", "c28"]
