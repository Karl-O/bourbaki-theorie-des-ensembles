"""Critères logiques C7–C25 de Bourbaki (chap. I §3), comme tactiques vérifiées.

Issus de la couverture multi-agents (Phase A), re-vérifiés ici par le noyau à
chaque exécution de la suite. Trois statuts honnêtes :
  * THÉORÈME CLOS : produit un Theoreme clos dont .conclusion est l'énoncé exact ;
  * RÈGLE : prend des prémisses (Theoreme) et produit le conséquent (séquent) ;
  * (C14 = loi_deduction est une primitive de confiance du noyau, pas dérivée.)

Non couverts (métathéorèmes hors fragment objet) : C2–C5, C19. Voir couverture.py.
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import (negation, disjonction, implication, conjonction, equivalence)
from bourbaki.logique.lecture import DEFAUT
from bourbaki.logique import noyau
from bourbaki.logique.tactiques.tactiques import (a_implique_a, syllogisme, affaiblissement,
                       mono_gauche, mono_droite, antecedent_consequent)
from bourbaki.logique.tactiques.tactiques_prop import (
    tiers_exclu, double_negation_intro, double_negation_elim, contraposition,
    contraposition_theoreme, conjonction_intro, projection_gauche, projection_droite,
    equivalence_avant, equivalence_arriere)


# ── Théorèmes clos ────────────────────────────────────────────────────────────

def c7(a, b, sig=DEFAUT):
    """⊢ B ⇒ (A ∨ B).  (S2, S3, syllogisme.)"""
    return syllogisme(noyau.s2(b, a, sig), noyau.s3(b, a, sig), sig)


c10 = tiers_exclu                 # ⊢ A ∨ ¬A
c11 = double_negation_intro       # ⊢ A ⇒ ¬¬A
c12 = contraposition_theoreme     # ⊢ (A⇒B) ⇒ (¬B⇒¬A)
c16 = double_negation_elim        # ⊢ ¬¬A ⇒ A
c21g = projection_gauche          # ⊢ (A et B) ⇒ A
c21d = projection_droite          # ⊢ (A et B) ⇒ B


def c17(a, b, sig=DEFAUT):
    """⊢ ((¬B ⇒ ¬A) ⇒ (A ⇒ B))."""
    h = noyau.assume(implication(negation(b), negation(a)), sig)
    t = syllogisme(double_negation_intro(a, sig), contraposition(h, sig), sig)  # {H}⊢A⇒¬¬B
    t = syllogisme(t, double_negation_elim(b, sig), sig)                        # {H}⊢A⇒B
    return noyau.loi_deduction(implication(negation(b), negation(a)), t, sig)


def c24_double_negation(a, sig=DEFAUT):
    """⊢ (¬¬A) ⇔ A.  (un représentant de la liste C24.)"""
    return conjonction_intro(double_negation_elim(a, sig),
                             double_negation_intro(a, sig), sig)


# ── Règles (prémisses Theoreme → conséquent) ──────────────────────────────────

c9 = affaiblissement              # Γ⊢B ⟹ Γ⊢ A⇒B
c20 = conjonction_intro           # ⊢A, ⊢B ⟹ ⊢ A et B
c14 = noyau.loi_deduction         # C14 = théorème de la déduction (primitive de confiance)


def c13(thm_ab, c, sig=DEFAUT):
    """⊢ A⇒B  ⟹  ⊢ (B⇒C) ⇒ (A⇒C)."""
    _, b = antecedent_consequent(thm_ab.conclusion, sig)
    hbc = noyau.assume(implication(b, c), sig)
    return noyau.loi_deduction(implication(b, c), syllogisme(thm_ab, hbc, sig), sig)


def c15(thm_nota_a, a, sig=DEFAUT):
    """⊢ (¬A ⇒ A)  ⟹  ⊢ A.  (cœur d'inférence du raisonnement par l'absurde.)"""
    aa = noyau.modus_ponens(tiers_exclu(a, sig), mono_droite(thm_nota_a, a, sig), sig)
    return noyau.modus_ponens(aa, noyau.s1(a, sig), sig)


def c18(t_or, t_ac, t_bc, sig=DEFAUT):
    """⊢ A∨B, ⊢ A⇒C, ⊢ B⇒C  ⟹  ⊢ C.  (disjonction des cas.)"""
    _, c = antecedent_consequent(t_ac.conclusion, sig)
    b, _ = antecedent_consequent(t_bc.conclusion, sig)
    t = syllogisme(mono_gauche(t_ac, b, sig), mono_droite(t_bc, c, sig), sig)  # (A∨B)⇒(C∨C)
    t = syllogisme(t, noyau.s1(c, sig), sig)                                   # (A∨B)⇒C
    return noyau.modus_ponens(t_or, t, sig)


def c22_symetrie(thm_eq, sig=DEFAUT):
    """Γ⊢ (A⇔B)  ⟹  Γ⊢ (B⇔A)."""
    return conjonction_intro(equivalence_arriere(thm_eq, sig),
                             equivalence_avant(thm_eq, sig), sig)


def c22_transitivite(thm_ab, thm_bc, sig=DEFAUT):
    """Γ⊢ (A⇔B), Δ⊢ (B⇔C)  ⟹  Γ∪Δ⊢ (A⇔C)."""
    ac = syllogisme(equivalence_avant(thm_ab, sig), equivalence_avant(thm_bc, sig), sig)
    ca = syllogisme(equivalence_arriere(thm_bc, sig), equivalence_arriere(thm_ab, sig), sig)
    return conjonction_intro(ac, ca, sig)


def c23_negation(thm_eq, sig=DEFAUT):
    """Γ⊢ (A⇔B)  ⟹  Γ⊢ (¬A ⇔ ¬B).  (cas négation de C23.)"""
    nb_na = contraposition(equivalence_avant(thm_eq, sig), sig)   # ¬B⇒¬A
    na_nb = contraposition(equivalence_arriere(thm_eq, sig), sig)  # ¬A⇒¬B
    return conjonction_intro(na_nb, nb_na, sig)


def c25_premier(thm_a, b, sig=DEFAUT):
    """⊢ A (théorème), B relation  ⟹  ⊢ (A et B) ⇔ B.  (premier cas de C25.)"""
    a = thm_a.conclusion
    avant = projection_droite(a, b, sig)                          # (A et B)⇒B
    hb = noyau.assume(b, sig)
    arriere = noyau.loi_deduction(b, conjonction_intro(thm_a, hb, sig), sig)  # B⇒(A et B)
    return conjonction_intro(avant, arriere, sig)


__all__ = ["c7", "c9", "c10", "c11", "c12", "c13", "c14", "c15", "c16", "c17",
           "c18", "c20", "c21g", "c21d", "c22_symetrie", "c22_transitivite",
           "c23_negation", "c24_double_negation", "c25_premier"]
