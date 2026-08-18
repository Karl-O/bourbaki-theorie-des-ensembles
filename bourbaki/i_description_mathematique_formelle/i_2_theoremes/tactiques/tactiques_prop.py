"""Couche 3 (suite) — boîte à outils propositionnelle classique.

PDF p.~25--30, Bourbaki, Chap. I §3.

Double négation, contraposition, syllogisme disjonctif, conjonction. TOUTES
ces règles sont **dérivées de S1–S4 + MP** (rien ajouté à la base de confiance ;
seul C6/déduction, déjà utilisé par `syllogisme`, reste primitif). Chaque
fonction renvoie un `Theoreme` vérifié par le noyau.

Rappels d'assemblage :  A⇒B = ¬A∨B  ;  A et B = ¬(¬A∨¬B).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.assemblage import Assemblage, negation, disjonction, implication
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.i_1_app_lecture import Signature, DEFAUT, depuis_assemblage, vers_assemblage
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau.noyau import Theoreme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques import (
    antecedent_consequent, affaiblissement, a_implique_a,
    syllogisme, distribution, mono_gauche,
)


# @livre Ch.I §3 Crit.11 | E I.26 L.18-18 | PDF p.26
# @livre Ch.I §3 Demo.- | E I.26 L.19-20 | PDF p.26  (démo de C11 : A⇒(non non A) n'est autre que « (non A) ou (non non A) », d'où C10)
def double_negation_intro(a: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ A ⇒ ¬¬A.  (¬A⇒¬A est ¬¬A∨¬A ; on commute par S3.)"""
    t = a_implique_a(negation(a), sig)          # ⊢ ¬A⇒¬A  =  ¬¬A ∨ ¬A
    s3 = noyau.s3(negation(negation(a)), negation(a), sig)  # (¬¬A∨¬A)⇒(¬A∨¬¬A)
    return noyau.modus_ponens(t, s3, sig)       # ⊢ ¬A∨¬¬A  =  A⇒¬¬A


# @livre Ch.I §3 Crit.16 | E I.28 L.7-7 | PDF p.28
# @livre Ch.I §3 Demo.- | E I.28 L.8-10 | PDF p.28  (démo de C16 par l'absurde : « non non A » et « non A » théorèmes ⇒ absurde)
def double_negation_elim(a: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ ¬¬A ⇒ A.  (À partir de ¬A∨A et de ¬A⇒¬¬¬A, mono-gauche.)"""
    em = a_implique_a(a, sig)                   # ⊢ A⇒A  =  ¬A ∨ A
    dni = double_negation_intro(negation(a), sig)  # ⊢ ¬A ⇒ ¬¬¬A
    lm = mono_gauche(dni, a, sig)               # (¬A∨A) ⇒ (¬¬¬A∨A)
    return noyau.modus_ponens(em, lm, sig)      # ⊢ ¬¬¬A∨A  =  ¬¬A⇒A


# @livre Ch.I §3 Crit.12 | E I.26 L.21-23 | PDF p.26
# @livre Ch.I §3 Demo.- | E I.26 L.24-30 | PDF p.26  (démo de C12, trois formules affichées : C11+S4+C1, puis S3, puis C6)
def contraposition(thm_pq: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ P⇒Q  ⟹  ⊢ ¬Q ⇒ ¬P.  Constructive (S3 + mono-gauche + dni)."""
    p, q = antecedent_consequent(thm_pq.conclusion, sig)
    comm = noyau.modus_ponens(thm_pq, noyau.s3(negation(p), q, sig), sig)  # ⊢ Q∨¬P
    lm = mono_gauche(double_negation_intro(q, sig), negation(p), sig)      # (Q∨¬P)⇒(¬¬Q∨¬P)
    return noyau.modus_ponens(comm, lm, sig)    # ⊢ ¬¬Q∨¬P  =  ¬Q⇒¬P


# @livre Ch.I §3 Crit.24 | E I.31 L.24-24 | PDF p.31
def syllogisme_disjonctif(p: Assemblage, q: Assemblage,
                          sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (P∨Q) ⇒ (¬P ⇒ Q).  (mono-gauche de dni : ¬P⇒Q = ¬¬P∨Q.)"""
    return mono_gauche(double_negation_intro(p, sig), q, sig)


# @livre Ch.I §3 Crit.20 | E I.29 L.20-20 | PDF p.29
# @livre Ch.I §3 Demo.- | E I.29 L.21-24 | PDF p.29  (démo de C20 par l'absurde : C16 donne A⇒(non B), donc « non B » vraie — absurde)
def conjonction_intro(thm_a: Theoreme, thm_b: Theoreme,
                      sig: Signature = DEFAUT) -> Theoreme:
    """⊢ A,  ⊢ B  ⟹  ⊢ (A et B).  (A et B = ¬(¬A∨¬B).)

    Preuve : nnA=⊢¬¬A, nnB=⊢¬¬B ; le syllogisme disjonctif donne
    ⊢(¬A∨¬B)⇒(¬¬A⇒¬B) ; en y injectant ¬¬A (distribution) : ⊢(¬A∨¬B)⇒¬B ;
    contraposée : ⊢¬¬B⇒¬(¬A∨¬B) ; MP avec ¬¬B.
    """
    a, b = thm_a.conclusion, thm_b.conclusion
    nnA = noyau.modus_ponens(thm_a, double_negation_intro(a, sig), sig)  # ⊢ ¬¬A
    nnB = noyau.modus_ponens(thm_b, double_negation_intro(b, sig), sig)  # ⊢ ¬¬B
    H = disjonction(negation(a), negation(b))                            # ¬A∨¬B
    ds = syllogisme_disjonctif(negation(a), negation(b), sig)            # H⇒(¬¬A⇒¬B)
    affH = affaiblissement(nnA, H, sig)                                  # H⇒¬¬A
    h_nb = distribution(ds, affH, sig)                                   # H⇒¬B
    contra = contraposition(h_nb, sig)                                   # ¬¬B⇒¬H
    return noyau.modus_ponens(nnB, contra, sig)                          # ⊢ ¬H = A et B


# @livre Ch.I §3 Crit.- | E I.30 L.34-37 | PDF p.30
def equivalence_reflexive(a: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ A ⇔ A.  (= (A⇒A) et (A⇒A), conjonction de deux A⇒A.)"""
    aa = a_implique_a(a, sig)
    return conjonction_intro(aa, aa, sig)


# ── Élimination de la conjonction et de l'équivalence ─────────────────────────

def composantes_conjonction(c: Assemblage, sig: Signature = DEFAUT
                            ) -> tuple[Assemblage, Assemblage]:
    """Décompose A et B = ¬(¬A∨¬B) en (A, B)."""
    a = depuis_assemblage(c, sig)
    if not (a.tete == "NON" and a.enfants[0].tete == "OU"):
        raise ValueError("pas une conjonction ¬(¬A∨¬B)")
    g, d = a.enfants[0].enfants
    if not (g.tete == "NON" and d.tete == "NON"):
        raise ValueError("pas une conjonction ¬(¬A∨¬B)")
    return vers_assemblage(g.enfants[0]), vers_assemblage(d.enfants[0])


# @livre Ch.I §3 Crit.21 | E I.29 L.25-26 | PDF p.29
# @livre Ch.I §3 Demo.- | E I.29 L.27-35 | PDF p.29  (démo de C21, cinq formules affichées : S2+C7, puis C11, puis C17)
def projection_gauche(a: Assemblage, b: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (A et B) ⇒ A.  (contraposée de S2 ¬A⇒(¬A∨¬B), puis DNE.)"""
    s2 = noyau.s2(negation(a), negation(b), sig)            # ¬A⇒(¬A∨¬B)
    return syllogisme(contraposition(s2, sig), double_negation_elim(a, sig), sig)


# @livre Ch.I §3 Crit.21 | E I.29 L.25-26 | PDF p.29
def projection_droite(a: Assemblage, b: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (A et B) ⇒ B."""
    t = syllogisme(noyau.s2(negation(b), negation(a), sig),
                   noyau.s3(negation(b), negation(a), sig), sig)  # ¬B⇒(¬A∨¬B)
    return syllogisme(contraposition(t, sig), double_negation_elim(b, sig), sig)


# @livre Ch.I §3 Crit.21 | E I.29 L.25-26 | PDF p.29
def conjonction_elim_gauche(thm: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """Γ ⊢ (A et B)  ⟹  Γ ⊢ A."""
    a, b = composantes_conjonction(thm.conclusion, sig)
    return noyau.modus_ponens(thm, projection_gauche(a, b, sig), sig)


# @livre Ch.I §3 Crit.21 | E I.29 L.25-26 | PDF p.29
def conjonction_elim_droite(thm: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """Γ ⊢ (A et B)  ⟹  Γ ⊢ B."""
    a, b = composantes_conjonction(thm.conclusion, sig)
    return noyau.modus_ponens(thm, projection_droite(a, b, sig), sig)


# @livre Ch.I §3 Crit.- | E I.30 L.34-37 | PDF p.30
def equivalence_avant(thm_equiv: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """Γ ⊢ (A ⇔ B)  ⟹  Γ ⊢ (A ⇒ B).  (projection gauche de la conjonction.)"""
    return conjonction_elim_gauche(thm_equiv, sig)


# @livre Ch.I §3 Crit.- | E I.30 L.34-37 | PDF p.30
def equivalence_arriere(thm_equiv: Theoreme, sig: Signature = DEFAUT) -> Theoreme:
    """Γ ⊢ (A ⇔ B)  ⟹  Γ ⊢ (B ⇒ A)."""
    return conjonction_elim_droite(thm_equiv, sig)


# @livre Ch.I §3 Crit.- | E I.30 L.34-37 | PDF p.30
def equivalence_modus(thm_equiv: Theoreme, thm_a: Theoreme,
                      sig: Signature = DEFAUT) -> Theoreme:
    """Γ ⊢ (A ⇔ B),  Δ ⊢ A  ⟹  Γ∪Δ ⊢ B."""
    return noyau.modus_ponens(thm_a, equivalence_avant(thm_equiv, sig), sig)


# ── Théorèmes propositionnels nommés (clos) ──────────────────────────────────

# @livre Ch.I §3 Crit.10 | E I.26 L.15-15 | PDF p.26
# @livre Ch.I §3 Demo.- | E I.26 L.16-17 | PDF p.26  (démo de C10 : « (non A) ou A » par C8, puis S3 + C1)
def tiers_exclu(a: Assemblage, sig: Signature = DEFAUT) -> Theoreme:
    """⊢ A ∨ ¬A.  (de A⇒A = ¬A∨A, commuté par S3.)"""
    return noyau.modus_ponens(a_implique_a(a, sig),
                              noyau.s3(negation(a), a, sig), sig)


# @livre Ch.I §3 Crit.12 | E I.26 L.21-23 | PDF p.26
def contraposition_theoreme(a: Assemblage, b: Assemblage,
                            sig: Signature = DEFAUT) -> Theoreme:
    """⊢ (A ⇒ B) ⇒ (¬B ⇒ ¬A).  (contraposition internalisée via C6.)"""
    h = noyau.assume(implication(a, b), sig)
    return noyau.loi_deduction(implication(a, b), contraposition(h, sig), sig)


__all__ = [
    "double_negation_intro", "double_negation_elim", "contraposition",
    "syllogisme_disjonctif", "conjonction_intro", "equivalence_reflexive",
    "composantes_conjonction", "projection_gauche", "projection_droite",
    "conjonction_elim_gauche", "conjonction_elim_droite",
    "equivalence_avant", "equivalence_arriere", "equivalence_modus",
    "tiers_exclu", "contraposition_theoreme",
]
