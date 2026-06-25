"""Congruence sous quantificateur — le verrou de C29, C31–C42 (Bourbaki §I.4.3).

Idée clé (route DIRECTE pour ∃, évitant la circularité C29) : pour la
monotonie de ∃, on utilise C30 GÉNÉRAL avec le terme témoin τ_x(R), puis S5.

  monotonie_existe : ⊢ R⇒S  ⟹  ⊢ (∃x)R ⇒ (∃x)S
    1. ⊢(∀x)(R⇒S)                       (généralisation C27)
    2. ⊢(∀x)(R⇒S) ⇒ (τxR|x)(R⇒S)        (C30 général, terme τxR)
    3. MP → ⊢ (∃x)R ⇒ (τxR|x)S          car (τxR|x)(R⇒S)=(∃x)R⇒(τxR|x)S [CS5]
    4. ⊢ (τxR|x)S ⇒ (∃x)S               (S5, terme τxR)
    5. syllogisme → ⊢ (∃x)R ⇒ (∃x)S

  monotonie_pour_tout : ⊢ R⇒S ⟹ ⊢ (∀x)R⇒(∀x)S  (instanciation + généralisation)
  congruence_*        : applique la monotonie aux deux sens de R⇔S
  C29                 : ¬(∃x)R ⇔ (∀x)¬R  (congruence-∃ sur R⇔¬¬R + négation)
"""
from __future__ import annotations

from bourbaki.assemblage.assemblage import (negation, implication, existe, pour_tout, tau_x)
from bourbaki.logique.i_1_termes_relations.lecture import DEFAUT
from bourbaki.logique.i_2_criteres_C.noyau import noyau
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques import syllogisme, antecedent_consequent
from bourbaki.logique.i_2_criteres_C.tactiques.tactiques_prop import conjonction_intro, equivalence_avant, equivalence_arriere
from bourbaki.logique.i_4_egalitaires.tactiques_egalite import instanciation, instanciation_en_x
from bourbaki.logique.i_2_criteres_C.criteres import criteres_C as K


# @livre Ch.I §4.3 Crit.31 | E I.34 L.20-22 | PDF p.34
def monotonie_existe(thm_rs, x, sig=DEFAUT):
    """⊢ R⇒S  ⟹  ⊢ (∃x)R ⇒ (∃x)S."""
    r, s = antecedent_consequent(thm_rs.conclusion, sig)
    gen = noyau.generalisation(x, thm_rs, sig)                 # ⊢ (∀x)(R⇒S)
    t = tau_x(r, x)                                            # témoin τx(R)
    mid = noyau.modus_ponens(gen, instanciation(implication(r, s), t, x, sig), sig)
    return syllogisme(mid, noyau.s5(s, t, x, sig), sig)        # ⊢ (∃x)R ⇒ (∃x)S


# @livre Ch.I §4.3 Crit.31 | E I.34 L.20-22 | PDF p.34
def monotonie_pour_tout(thm_rs, x, sig=DEFAUT):
    """⊢ R⇒S  ⟹  ⊢ (∀x)R ⇒ (∀x)S."""
    r, s = antecedent_consequent(thm_rs.conclusion, sig)
    h = noyau.assume(pour_tout(x, r), sig)                     # {(∀x)R} ⊢ (∀x)R
    hr = noyau.modus_ponens(h, instanciation_en_x(r, x, sig), sig)  # {(∀x)R} ⊢ R
    hs = noyau.modus_ponens(hr, thm_rs, sig)                   # {(∀x)R} ⊢ S
    return noyau.loi_deduction(pour_tout(x, r),
                               noyau.generalisation(x, hs, sig), sig)  # ⊢ (∀x)R⇒(∀x)S


# @livre Ch.I §4.3 Crit.31 | E I.34 L.20-22 | PDF p.34
def congruence_existe(thm_eq, x, sig=DEFAUT):
    """⊢ R⇔S  ⟹  ⊢ (∃x)R ⇔ (∃x)S."""
    return conjonction_intro(monotonie_existe(equivalence_avant(thm_eq, sig), x, sig),
                             monotonie_existe(equivalence_arriere(thm_eq, sig), x, sig), sig)


# @livre Ch.I §4.3 Crit.31 | E I.34 L.20-22 | PDF p.34
def congruence_pour_tout(thm_eq, x, sig=DEFAUT):
    """⊢ R⇔S  ⟹  ⊢ (∀x)R ⇔ (∀x)S."""
    return conjonction_intro(monotonie_pour_tout(equivalence_avant(thm_eq, sig), x, sig),
                             monotonie_pour_tout(equivalence_arriere(thm_eq, sig), x, sig), sig)


# @livre Ch.I §4.3 Crit.29 | E I.33 L.30-31 | PDF p.33
def c29(r, x, sig=DEFAUT):
    """⊢ ¬(∃x)R ⇔ (∀x)(¬R).  (congruence-∃ sur R⇔¬¬R, puis négation et symétrie.)"""
    cong = congruence_existe(K.c24_double_negation(r, sig), x, sig)  # (∃x)¬¬R ⇔ (∃x)R
    neg = K.c23_negation(cong, sig)        # ¬(∃x)¬¬R ⇔ ¬(∃x)R  =  (∀x)¬R ⇔ ¬(∃x)R
    return K.c22_symetrie(neg, sig)        # ¬(∃x)R ⇔ (∀x)¬R


__all__ = ["monotonie_existe", "monotonie_pour_tout",
           "congruence_existe", "congruence_pour_tout", "c29"]
