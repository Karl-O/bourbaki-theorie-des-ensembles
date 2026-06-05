# -*- coding: utf-8 -*-
"""Vérification C24 : les 13 équivalences classiques closes via le noyau V9."""
import sys

import propositions
from propositions import SIG_PROP as SIG, A, B, C
from assemblage import (negation, disjonction, implication, conjonction,
                        equivalence)
import noyau
from tactiques import (a_implique_a, syllogisme, affaiblissement,
                       mono_gauche, mono_droite, antecedent_consequent)
from tactiques_prop import (
    double_negation_intro, double_negation_elim, contraposition,
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    projection_gauche, projection_droite, syllogisme_disjonctif, tiers_exclu,
)
from criteres_C import c7, c17, c18

resultats = {}


from notation import afficher

def verifie(nom, attendu, fab):
    """fab() -> Theoreme ; on vérifie .conclusion == attendu et .est_clos."""
    try:
        thm = fab()
        ok = (thm.conclusion == attendu) and thm.est_clos and not thm.hypotheses
        rendu = afficher(thm.conclusion, SIG)
        resultats[nom] = (ok, rendu if ok else
                          f"conclusion={thm.conclusion!r} clos={thm.est_clos} hyp={thm.hypotheses}")
    except Exception as e:
        resultats[nom] = (False, f"{type(e).__name__}: {e}")


def equiv_de(xy_thm, yx_thm):
    """conjonction des deux implications -> X⇔Y."""
    return conjonction_intro(xy_thm, yx_thm, SIG)


# ─────────────────────────────────────────────────────────────────────────
# 1. (¬¬A) ⇔ A
def f1():
    av = double_negation_elim(A, SIG)        # ¬¬A ⇒ A
    ar = double_negation_intro(A, SIG)       # A ⇒ ¬¬A
    return equiv_de(av, ar)
verifie("1 (¬¬A)⇔A", equivalence(negation(negation(A)), A), f1)


# 2. (A⇒B) ⇔ (¬B⇒¬A)
def f2():
    # avant : (A⇒B) ⇒ (¬B⇒¬A)  via c12
    from criteres_C import c12
    av = c12(A, B, SIG)
    # arriere : (¬B⇒¬A) ⇒ (A⇒B)  via c17
    ar = c17(A, B, SIG)
    return equiv_de(av, ar)
verifie("2 (A⇒B)⇔(¬B⇒¬A)",
        equivalence(implication(A, B), implication(negation(B), negation(A))), f2)


# 3. (A et A) ⇔ A
def f3():
    # avant : (A et A) ⇒ A  = projection_gauche
    av = projection_gauche(A, A, SIG)
    # arriere : A ⇒ (A et A) : sous hyp A, conj_intro(A,A), déduction
    hA = noyau.assume(A, SIG)
    ar = noyau.loi_deduction(A, conjonction_intro(hA, hA, SIG), SIG)
    return equiv_de(av, ar)
verifie("3 (A et A)⇔A", equivalence(conjonction(A, A), A), f3)


# 4. (A et B) ⇔ (B et A)
def f4():
    # avant : (A et B) ⇒ (B et A)
    hAB = noyau.assume(conjonction(A, B), SIG)
    ga = conjonction_elim_gauche(hAB, SIG)   # {AetB} ⊢ A
    gb = conjonction_elim_droite(hAB, SIG)   # {AetB} ⊢ B
    av = noyau.loi_deduction(conjonction(A, B), conjonction_intro(gb, ga, SIG), SIG)
    # arriere : (B et A) ⇒ (A et B)
    hBA = noyau.assume(conjonction(B, A), SIG)
    gb2 = conjonction_elim_gauche(hBA, SIG)  # B
    ga2 = conjonction_elim_droite(hBA, SIG)  # A
    ar = noyau.loi_deduction(conjonction(B, A), conjonction_intro(ga2, gb2, SIG), SIG)
    return equiv_de(av, ar)
verifie("4 (A et B)⇔(B et A)",
        equivalence(conjonction(A, B), conjonction(B, A)), f4)


# 5. (A et (B et C)) ⇔ ((A et B) et C)
def f5():
    # avant
    h = noyau.assume(conjonction(A, conjonction(B, C)), SIG)
    a = conjonction_elim_gauche(h, SIG)            # A
    bc = conjonction_elim_droite(h, SIG)           # B et C
    b = conjonction_elim_gauche(bc, SIG)           # B
    c = conjonction_elim_droite(bc, SIG)           # C
    ab = conjonction_intro(a, b, SIG)              # A et B
    res = conjonction_intro(ab, c, SIG)            # (A et B) et C
    av = noyau.loi_deduction(conjonction(A, conjonction(B, C)), res, SIG)
    # arriere
    h2 = noyau.assume(conjonction(conjonction(A, B), C), SIG)
    ab2 = conjonction_elim_gauche(h2, SIG)         # A et B
    c2 = conjonction_elim_droite(h2, SIG)          # C
    a2 = conjonction_elim_gauche(ab2, SIG)         # A
    b2 = conjonction_elim_droite(ab2, SIG)         # B
    bc2 = conjonction_intro(b2, c2, SIG)           # B et C
    res2 = conjonction_intro(a2, bc2, SIG)         # A et (B et C)
    ar = noyau.loi_deduction(conjonction(conjonction(A, B), C), res2, SIG)
    return equiv_de(av, ar)
verifie("5 assoc et",
        equivalence(conjonction(A, conjonction(B, C)),
                    conjonction(conjonction(A, B), C)), f5)


# 6. (A ou B) ⇔ ¬(¬A et ¬B)   [De Morgan]
#    A ou B = disjonction(A,B).  ¬A et ¬B = conjonction(¬A,¬B).
def f6():
    # conjonction(¬A,¬B) = ¬(¬¬A ∨ ¬¬B).  Donc ¬(¬A et ¬B) = ¬¬(¬¬A ∨ ¬¬B).
    # avant : (A∨B) ⇒ ¬(¬A et ¬B)
    # ¬(¬A et ¬B) = ¬conjonction(¬A,¬B).  conjonction(¬A,¬B) ⇒ ¬A (proj) ... on construit.
    # Stratégie : A∨B ⇒ ¬¬(¬¬A∨¬¬B). On montre A∨B ⇒ (¬¬A∨¬¬B) puis dni.
    # mono : A⇒¬¬A donne (A∨B)⇒(¬¬A∨B) ; B⇒¬¬B donne (¬¬A∨B)⇒(¬¬A∨¬¬B).
    t1 = mono_gauche(double_negation_intro(A, SIG), B, SIG)          # (A∨B)⇒(¬¬A∨B)
    t2 = mono_droite(double_negation_intro(B, SIG), negation(negation(A)), SIG)  # (¬¬A∨B)⇒(¬¬A∨¬¬B)
    t3 = syllogisme(t1, t2, SIG)                                     # (A∨B)⇒(¬¬A∨¬¬B)
    dni = double_negation_intro(disjonction(negation(negation(A)),
                                            negation(negation(B))), SIG)  # (¬¬A∨¬¬B)⇒¬¬(¬¬A∨¬¬B)
    av = syllogisme(t3, dni, SIG)   # (A∨B) ⇒ ¬¬(¬¬A∨¬¬B) = ¬(¬A et ¬B)
    # arriere : ¬(¬A et ¬B) ⇒ (A∨B)
    # ¬(¬A et ¬B) = ¬¬(¬¬A∨¬¬B) ; dne -> (¬¬A∨¬¬B) ; puis ¬¬A⇒A, ¬¬B⇒B mono -> (A∨B)
    dne = double_negation_elim(disjonction(negation(negation(A)),
                                           negation(negation(B))), SIG)  # ¬¬(..)⇒(¬¬A∨¬¬B)
    u1 = mono_gauche(double_negation_elim(A, SIG), negation(negation(B)), SIG)  # (¬¬A∨¬¬B)⇒(A∨¬¬B)
    u2 = mono_droite(double_negation_elim(B, SIG), A, SIG)           # (A∨¬¬B)⇒(A∨B)
    ar = syllogisme(syllogisme(dne, u1, SIG), u2, SIG)
    return equiv_de(av, ar)
verifie("6 De Morgan (A ou B)⇔¬(¬A et ¬B)",
        equivalence(disjonction(A, B),
                    negation(conjonction(negation(A), negation(B)))), f6)


# 7. (A ou A) ⇔ A
def f7():
    # avant : (A∨A) ⇒ A  = S1
    av = noyau.s1(A, SIG)
    # arriere : A ⇒ (A∨A) = S2
    ar = noyau.s2(A, A, SIG)
    return equiv_de(av, ar)
verifie("7 (A ou A)⇔A", equivalence(disjonction(A, A), A), f7)


# 8. (A ou B) ⇔ (B ou A)
def f8():
    av = noyau.s3(A, B, SIG)   # (A∨B)⇒(B∨A)
    ar = noyau.s3(B, A, SIG)   # (B∨A)⇒(A∨B)
    return equiv_de(av, ar)
verifie("8 (A ou B)⇔(B ou A)",
        equivalence(disjonction(A, B), disjonction(B, A)), f8)


# 9. (A ou (B ou C)) ⇔ ((A ou B) ou C)
def f9():
    # avant : A∨(B∨C) ⇒ (A∨B)∨C, via disjonction des cas C18.
    # Rappel convention : c7(g, x) = ⊢ x ⇒ (g ∨ x).
    AB = disjonction(A, B)
    BC = disjonction(B, C)
    # ── avant : A∨(B∨C) ⇒ (A∨B)∨C
    aABC = syllogisme(noyau.s2(A, B, SIG), noyau.s2(AB, C, SIG), SIG)   # A⇒(A∨B)∨C
    bABC = syllogisme(c7(A, B, SIG), noyau.s2(AB, C, SIG), SIG)         # B⇒(A∨B)∨C
    cABC = c7(AB, C, SIG)                                               # C⇒(A∨B)∨C
    bc_to = _or_to(BC, B, C, bABC, cABC, SIG)                           # (B∨C)⇒(A∨B)∨C
    h = noyau.assume(disjonction(A, BC), SIG)
    res = c18(h, aABC, bc_to, SIG)
    av = noyau.loi_deduction(disjonction(A, BC), res, SIG)
    # ── arriere : (A∨B)∨C ⇒ A∨(B∨C)
    aBC = noyau.s2(A, BC, SIG)                                          # A⇒A∨(B∨C)
    bBC = syllogisme(noyau.s2(B, C, SIG), c7(A, BC, SIG), SIG)          # B⇒A∨(B∨C)
    cBC = syllogisme(c7(B, C, SIG), c7(A, BC, SIG), SIG)               # C⇒A∨(B∨C)
    ab_to = _or_to(AB, A, B, aBC, bBC, SIG)                             # (A∨B)⇒A∨(B∨C)
    h2 = noyau.assume(disjonction(AB, C), SIG)
    res2 = c18(h2, ab_to, cBC, SIG)
    ar = noyau.loi_deduction(disjonction(AB, C), res2, SIG)
    return equiv_de(av, ar)


def _or_to(xy, x, y, x_to, y_to, sig):
    """De ⊢ x⇒Z et ⊢ y⇒Z, construit ⊢ (x∨y)⇒Z (c18 sous hypothèse x∨y)."""
    hxy = noyau.assume(xy, sig)
    r = c18(hxy, x_to, y_to, sig)
    return noyau.loi_deduction(xy, r, sig)

verifie("9 assoc ou",
        equivalence(disjonction(A, disjonction(B, C)),
                    disjonction(disjonction(A, B), C)), f9)


# 10. (A et (B ou C)) ⇔ ((A et B) ou (A et C))   distributivité et/ou
def f10():
    # avant : A et (B∨C) ⇒ (A et B)∨(A et C)
    h = noyau.assume(conjonction(A, disjonction(B, C)), SIG)
    a = conjonction_elim_gauche(h, SIG)            # A
    bc = conjonction_elim_droite(h, SIG)           # B∨C
    # sous-cas via c18 sur bc : B ⇒ (AetB)∨(AetC) ; C ⇒ ...
    # need ⊢ A in this context to build conjonctions. We have a (Theoreme with hyp).
    hB = noyau.assume(B, SIG)
    caseB = noyau.loi_deduction(B,
              syllogisme_left_or(conjonction_intro(a, hB, SIG),
                                 conjonction(A, C), SIG), SIG)  # B⇒(AetB)∨(AetC)
    hC = noyau.assume(C, SIG)
    caseC = noyau.loi_deduction(C,
              syllogisme_right_or(conjonction_intro(a, hC, SIG),
                                  conjonction(A, B), SIG), SIG)  # C⇒(AetB)∨(AetC)
    res = c18(bc, caseB, caseC, SIG)
    av = noyau.loi_deduction(conjonction(A, disjonction(B, C)), res, SIG)
    # arriere : (A et B)∨(A et C) ⇒ A et (B∨C)
    h2 = noyau.assume(disjonction(conjonction(A, B), conjonction(A, C)), SIG)
    # AetB ⇒ A et (B∨C)
    hab = noyau.assume(conjonction(A, B), SIG)
    a1 = conjonction_elim_gauche(hab, SIG)
    b1 = conjonction_elim_droite(hab, SIG)
    bc1 = noyau.modus_ponens(b1, noyau.s2(B, C, SIG), SIG)   # B∨C
    target1 = conjonction_intro(a1, bc1, SIG)
    caseAB = noyau.loi_deduction(conjonction(A, B), target1, SIG)
    hac = noyau.assume(conjonction(A, C), SIG)
    a2 = conjonction_elim_gauche(hac, SIG)
    c2 = conjonction_elim_droite(hac, SIG)
    bc2 = noyau.modus_ponens(c2, c7(B, C, SIG), SIG)         # C⇒(B∨C)
    target2 = conjonction_intro(a2, bc2, SIG)
    caseAC = noyau.loi_deduction(conjonction(A, C), target2, SIG)
    res2 = c18(h2, caseAB, caseAC, SIG)
    ar = noyau.loi_deduction(disjonction(conjonction(A, B), conjonction(A, C)), res2, SIG)
    return equiv_de(av, ar)


def syllogisme_left_or(thm_x, q, sig):
    """⊢X ⟹ ⊢ X∨q (S2)."""
    return noyau.modus_ponens(thm_x, noyau.s2(thm_x.conclusion, q, sig), sig)


def syllogisme_right_or(thm_x, p, sig):
    """⊢X ⟹ ⊢ p∨X (c7 : c7(p,X) = X⇒(p∨X))."""
    return noyau.modus_ponens(thm_x, c7(p, thm_x.conclusion, sig), sig)

verifie("10 distrib et/ou",
        equivalence(conjonction(A, disjonction(B, C)),
                    disjonction(conjonction(A, B), conjonction(A, C))), f10)


# 11. (A ou (B et C)) ⇔ ((A ou B) et (A ou C))   distributivité ou/et
def f11():
    # avant : A∨(B et C) ⇒ (A∨B) et (A∨C)
    h = noyau.assume(disjonction(A, conjonction(B, C)), SIG)
    # cas A ⇒ (A∨B) et (A∨C)
    hA = noyau.assume(A, SIG)
    ab = noyau.modus_ponens(hA, noyau.s2(A, B, SIG), SIG)   # A∨B
    ac = noyau.modus_ponens(hA, noyau.s2(A, C, SIG), SIG)   # A∨C
    caseA = noyau.loi_deduction(A, conjonction_intro(ab, ac, SIG), SIG)
    # cas (B et C) ⇒ (A∨B) et (A∨C)
    hbc = noyau.assume(conjonction(B, C), SIG)
    b = conjonction_elim_gauche(hbc, SIG)
    c = conjonction_elim_droite(hbc, SIG)
    ab2 = noyau.modus_ponens(b, c7(A, B, SIG), SIG)         # B⇒(A∨B)
    ac2 = noyau.modus_ponens(c, c7(A, C, SIG), SIG)         # C⇒(A∨C)
    caseBC = noyau.loi_deduction(conjonction(B, C),
                                 conjonction_intro(ab2, ac2, SIG), SIG)
    res = c18(h, caseA, caseBC, SIG)
    av = noyau.loi_deduction(disjonction(A, conjonction(B, C)), res, SIG)
    # arriere : (A∨B) et (A∨C) ⇒ A∨(B et C)
    h2 = noyau.assume(conjonction(disjonction(A, B), disjonction(A, C)), SIG)
    aOrB = conjonction_elim_gauche(h2, SIG)   # A∨B
    aOrC = conjonction_elim_droite(h2, SIG)   # A∨C
    # cas distinction sur A∨B : A ⇒ goal ; B ⇒ (need A∨C) ...
    goal = disjonction(A, conjonction(B, C))
    # A ⇒ A∨(B et C)
    hA2 = noyau.assume(A, SIG)
    cA = noyau.loi_deduction(A, noyau.modus_ponens(hA2, noyau.s2(A, conjonction(B, C), SIG), SIG), SIG)
    # B ⇒ A∨(B et C)  — under hyp aOrC: from A∨C, cases A->goal, C-> B et C -> goal
    hB2 = noyau.assume(B, SIG)
    #   subcase from aOrC
    hA3 = noyau.assume(A, SIG)
    cA3 = noyau.loi_deduction(A, noyau.modus_ponens(hA3, noyau.s2(A, conjonction(B, C), SIG), SIG), SIG)
    hC3 = noyau.assume(C, SIG)
    bc_c = conjonction_intro(hB2, hC3, SIG)   # {B,C} ⊢ B et C
    goal_from_C = noyau.modus_ponens(bc_c, c7(A, conjonction(B, C), SIG), SIG)  # (B et C)⇒A∨(B et C)
    cC3 = noyau.loi_deduction(C, goal_from_C, SIG)   # {B} ⊢ C ⇒ goal
    # disjonction des cas on aOrC giving {B} ⊢ goal
    goalB = c18(aOrC, cA3, cC3, SIG)          # {A∨C across, B} ⊢ goal ; carries hyp B and (A∨B),(A∨C)
    cB = noyau.loi_deduction(B, goalB, SIG)   # ⊢ B ⇒ goal (under remaining hyps)
    res2 = c18(aOrB, cA, cB, SIG)
    ar = noyau.loi_deduction(conjonction(disjonction(A, B), disjonction(A, C)), res2, SIG)
    return equiv_de(av, ar)
verifie("11 distrib ou/et",
        equivalence(disjonction(A, conjonction(B, C)),
                    conjonction(disjonction(A, B), disjonction(A, C))), f11)


# 12. (A et ¬B) ⇔ ¬(A⇒B)
def f12():
    # A⇒B = ¬A∨B.  ¬(A⇒B) = ¬(¬A∨B).
    # A et ¬B = ¬(¬A∨¬¬B) = conjonction(A, ¬B).
    # avant : (A et ¬B) ⇒ ¬(A⇒B)
    h = noyau.assume(conjonction(A, negation(B)), SIG)
    a = conjonction_elim_gauche(h, SIG)       # A
    nb = conjonction_elim_droite(h, SIG)      # ¬B
    # ¬(¬A∨B): show ¬¬A and ¬B then conj? Instead: ¬(A⇒B) = ¬(¬A∨B).
    # conjonction(¬¬A, ¬B) = ¬(¬¬¬A ∨ ¬¬B) -- not equal. Build ¬(¬A∨B) directly.
    # (¬A∨B) ⇒ ? we have A (so ¬¬A) and ¬B. (¬A∨B)⇒(¬¬A⇒B) syll disj; inject ¬¬A => B; contra ¬B⇒¬(¬A∨B).
    nna = noyau.modus_ponens(a, double_negation_intro(A, SIG), SIG)  # ¬¬A
    sd = syllogisme_disjonctif(negation(A), B, SIG)   # (¬A∨B)⇒(¬¬A⇒B)
    Hor = disjonction(negation(A), B)
    affH = affaiblissement(nna, Hor, SIG)             # Hor⇒¬¬A
    from tactiques import distribution
    h_b = distribution(sd, affH, SIG)                 # Hor⇒B
    contra = contraposition(h_b, SIG)                 # ¬B⇒¬Hor
    notimp = noyau.modus_ponens(nb, contra, SIG)      # ⊢ ¬(¬A∨B) = ¬(A⇒B)  (under hyp)
    av = noyau.loi_deduction(conjonction(A, negation(B)), notimp, SIG)
    # arriere : ¬(A⇒B) ⇒ (A et ¬B)
    h2 = noyau.assume(negation(implication(A, B)), SIG)   # ¬(¬A∨B)
    # derive A: from ¬(¬A∨B): ¬A ⇒ (¬A∨B) (S2) so contra (¬(¬A∨B)) ⇒ ¬¬A ⇒ A
    notor = h2
    s2a = noyau.s2(negation(A), B, SIG)               # ¬A⇒(¬A∨B)
    contra_a = contraposition(s2a, SIG)               # ¬(¬A∨B)⇒¬¬A
    nnA2 = noyau.modus_ponens(notor, contra_a, SIG)   # ¬¬A
    a2 = noyau.modus_ponens(nnA2, double_negation_elim(A, SIG), SIG)  # A
    # derive ¬B: B⇒(¬A∨B), contra ¬(¬A∨B)⇒¬B
    c7b = syllogisme(noyau.s2(B, negation(A), SIG),
                     noyau.s3(B, negation(A), SIG), SIG)   # B⇒(¬A∨B)
    contra_b = contraposition(c7b, SIG)               # ¬(¬A∨B)⇒¬B
    nb2 = noyau.modus_ponens(notor, contra_b, SIG)    # ¬B
    res2 = conjonction_intro(a2, nb2, SIG)
    ar = noyau.loi_deduction(negation(implication(A, B)), res2, SIG)
    return equiv_de(av, ar)
verifie("12 (A et ¬B)⇔¬(A⇒B)",
        equivalence(conjonction(A, negation(B)),
                    negation(implication(A, B))), f12)


# 13. (A ou B) ⇔ (¬A ⇒ B)
def f13():
    # A∨B = disjonction(A,B). ¬A⇒B = ¬¬A∨B.
    # avant : (A∨B) ⇒ (¬¬A∨B) : mono_gauche dni A
    av = mono_gauche(double_negation_intro(A, SIG), B, SIG)   # (A∨B)⇒(¬¬A∨B)
    # arriere : (¬¬A∨B) ⇒ (A∨B) : mono_gauche dne A
    ar = mono_gauche(double_negation_elim(A, SIG), B, SIG)    # (¬¬A∨B)⇒(A∨B)
    return equiv_de(av, ar)
verifie("13 (A ou B)⇔(¬A⇒B)",
        equivalence(disjonction(A, B), implication(negation(A), B)), f13)


# ─────────────────────────────────────────────────────────────────────────
for nom, (ok, note) in resultats.items():
    print(f"{'OK ' if ok else 'KO '} | {nom} | {note}")
