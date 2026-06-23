"""C24/C25 (suite 2) — équivalences plus longues, re-vérifiées par le noyau.

Complète le lock-in de la Phase B : associativité de « et », De Morgan,
(A et ¬B)⇔¬(A⇒B), et le 2ᵉ cas de C25. Restent workflow-vérifiées (lock-in à
finir) : associativité de « ou » et les deux distributivités (preuves très
longues par disjonction des cas imbriquée).
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import (negation, disjonction, conjonction, implication, equivalence)
from bourbaki.logique.i_1_termes_relations.lecture import DEFAUT
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques import a_implique_a, syllogisme, mono_gauche, mono_droite
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_prop import (double_negation_intro, double_negation_elim,
                            contraposition, conjonction_intro,
                            conjonction_elim_gauche, conjonction_elim_droite)
from bourbaki.logique.i_2_criteres_C.criteres import criteres_C as K


def c24_assoc_et(a, b, c, sig=DEFAUT):
    """⊢ (A et (B et C)) ⇔ ((A et B) et C)."""
    def avant():
        h = noyau.assume(conjonction(a, conjonction(b, c)), sig)
        x = conjonction_elim_gauche(h, sig)             # A
        bc = conjonction_elim_droite(h, sig)            # B et C
        res = conjonction_intro(
            conjonction_intro(x, conjonction_elim_gauche(bc, sig), sig),  # A et B
            conjonction_elim_droite(bc, sig), sig)                        # et C
        return noyau.loi_deduction(conjonction(a, conjonction(b, c)), res, sig)

    def arriere():
        h = noyau.assume(conjonction(conjonction(a, b), c), sig)
        ab = conjonction_elim_gauche(h, sig)            # A et B
        res = conjonction_intro(
            conjonction_elim_gauche(ab, sig),                              # A
            conjonction_intro(conjonction_elim_droite(ab, sig),            # B
                              conjonction_elim_droite(h, sig), sig), sig)  # et C
        return noyau.loi_deduction(conjonction(conjonction(a, b), c), res, sig)

    return conjonction_intro(avant(), arriere(), sig)


def c24_demorgan(a, b, sig=DEFAUT):
    """⊢ (A ou B) ⇔ ¬((¬A) et (¬B)).  (¬A et ¬B = ¬(¬¬A∨¬¬B).)"""
    naa, nnb = negation(negation(a)), negation(negation(b))
    nn = disjonction(naa, nnb)                              # ¬¬A ∨ ¬¬B
    # (A∨B) ⇒ (¬¬A∨¬¬B) ⇒ ¬¬(¬¬A∨¬¬B) = ¬(¬A et ¬B)
    t = syllogisme(mono_gauche(double_negation_intro(a, sig), b, sig),       # (A∨B)⇒(¬¬A∨B)
                   mono_droite(double_negation_intro(b, sig), naa, sig), sig)  # (¬¬A∨B)⇒(¬¬A∨¬¬B)
    av = syllogisme(t, double_negation_intro(nn, sig), sig)
    # ¬¬(¬¬A∨¬¬B) ⇒ (¬¬A∨¬¬B) ⇒ (A∨B)
    descend = syllogisme(mono_gauche(double_negation_elim(a, sig), nnb, sig),  # (¬¬A∨¬¬B)⇒(A∨¬¬B)
                         mono_droite(double_negation_elim(b, sig), a, sig), sig)  # (A∨¬¬B)⇒(A∨B)
    ar = syllogisme(double_negation_elim(nn, sig), descend, sig)
    return conjonction_intro(av, ar, sig)


def c24_et_non(a, b, sig=DEFAUT):
    """⊢ (A et ¬B) ⇔ ¬(A ⇒ B).  (A et ¬B = ¬(¬A∨¬¬B) ; A⇒B = ¬A∨B.)"""
    av = contraposition(mono_droite(double_negation_intro(b, sig), negation(a), sig), sig)
    ar = contraposition(mono_droite(double_negation_elim(b, sig), negation(a), sig), sig)
    return conjonction_intro(av, ar, sig)


def _ou_implique(p, q, imp_p, imp_q, sig):
    """De ⊢p⇒R et ⊢q⇒R, fabrique ⊢ (p∨q)⇒R  (via C18 sous hypothèse p∨q)."""
    h = noyau.assume(disjonction(p, q), sig)
    return noyau.loi_deduction(disjonction(p, q), K.c18(h, imp_p, imp_q, sig), sig)


def c25_second(thm_non_a, b, sig=DEFAUT):
    """⊢ ¬A  ⟹  ⊢ (A ou B) ⇔ B.  (2ᵉ cas de C25.)"""
    a = thm_non_a.conclusion.signes  # juste pour récupérer A via la négation
    # A = relation telle que thm_non_a : ⊢ ¬A. On reconstruit A par lecture.
    from bourbaki.logique.i_1_termes_relations.lecture import depuis_assemblage, vers_assemblage
    arbre = depuis_assemblage(thm_non_a.conclusion, sig)
    A = vers_assemblage(arbre.enfants[0])             # le R sous le ¬
    a_imp_b = noyau.modus_ponens(thm_non_a, noyau.s2(negation(A), b, sig), sig)  # ⊢ A⇒B
    av = _ou_implique(A, b, a_imp_b, a_implique_a(b, sig), sig)      # (A∨B)⇒B
    ar = syllogisme(noyau.s2(b, A, sig), noyau.s3(b, A, sig), sig)   # B⇒(A∨B)
    return conjonction_intro(av, ar, sig)


__all__ = ["c24_assoc_et", "c24_demorgan", "c24_et_non", "c25_second"]
