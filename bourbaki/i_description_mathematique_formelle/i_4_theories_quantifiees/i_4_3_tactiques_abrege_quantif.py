"""Couche quantifiée abrégée — monotonie et congruence sous ∀/∃, élimination de ∃.

Portage au niveau abrégé (∃ = nœud) des critères C31/C34 (monotonie) et de la
congruence sous quantificateur. La clé est `existe_temoin` (réciproque de S5 pour
le témoin τx(R)), qui permet de rejouer l'astuce τ : généraliser puis instancier
au témoin canonique. Tout est dérivé des primitives — aucune nouvelle confiance
au-delà de `existe_temoin`.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import var, non, et, impl, existe, pourtout, tau, subst_f, libres_f
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import antecedent_consequent, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (instanciation_en_x, instanciation, instancie, contraposition,
                               conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, equivalence_avant, equivalence_arriere)


# @livre Ch.I §4.3 Crit.31 | E I.34 L.20-22 | PDF p.34
def monotonie_pour_tout(thm_rs, x):
    """⊢ R⇒S (x non libre dans Γ) ⟹ Γ ⊢ (∀x)R ⇒ (∀x)S.  (demi-C31, ∀.)"""
    r, s = antecedent_consequent(thm_rs.conclusion)
    h = N.assume(pourtout(x, r))                       # x non libre dans (∀x)R
    rr = N.modus_ponens(h, instanciation_en_x(r, x))   # ⊢ R   (hyp (∀x)R)
    ss = N.modus_ponens(rr, thm_rs)                    # ⊢ S
    gen = N.generalisation(x, ss)                      # ⊢ (∀x)S
    return N.loi_deduction(pourtout(x, r), gen)


# @livre Ch.I §4.3 Crit.31 | E I.34 L.20-22 | PDF p.34
def monotonie_existe(thm_rs, x):
    """⊢ R⇒S (x non libre dans Γ) ⟹ Γ ⊢ (∃x)R ⇒ (∃x)S.  (demi-C31, ∃.)

    Astuce τ rejouée au niveau abrégé : (∀x)(R⇒S) instancié au témoin W=τx(R)."""
    r, s = antecedent_consequent(thm_rs.conclusion)
    w = tau(x, r)
    gen = N.generalisation(x, thm_rs)                  # ⊢ (∀x)(R⇒S)
    inst = instanciation(impl(r, s), w, x)             # (∀x)(R⇒S) ⇒ (W|x)(R⇒S)
    rw_sw = N.modus_ponens(gen, inst)                  # (W|x)R ⇒ (W|x)S
    sw_ex = N.s5(s, w, x)                              # (W|x)S ⇒ (∃x)S
    ex_rw = N.existe_temoin(r, x)                      # (∃x)R ⇒ (W|x)R
    return syllogisme(syllogisme(ex_rw, rw_sw), sw_ex)  # (∃x)R ⇒ (∃x)S


def existe_vacuous(c, x):
    """⊢ (∃x)C ⇒ C   lorsque x n'est pas libre dans C  (existentielle vide)."""
    if x in __import__("bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule", fromlist=["libres_f"]).libres_f(c):
        raise ValueError(f"{x!r} libre dans C : (∃x)C ⇒ C invalide")
    return N.existe_temoin(c, x)                        # (∃x)C ⇒ (τxC|x)C = C  (x∉C)


def existe_elimination(thm_rc, x):
    """Γ ⊢ R⇒C (x non libre dans C ni dans Γ) ⟹ Γ ⊢ (∃x)R ⇒ C."""
    _, c = antecedent_consequent(thm_rc.conclusion)
    return syllogisme(monotonie_existe(thm_rc, x), existe_vacuous(c, x))


# @livre Ch.I §4.3 Crit.31 | E I.34 L.20-22 | PDF p.34
def congruence_pour_tout(thm_eq, x):
    """⊢ (R⇔S) (x non libre dans Γ) ⟹ Γ ⊢ (∀x)R ⇔ (∀x)S."""
    avant = monotonie_pour_tout(equivalence_avant(thm_eq), x)
    arriere = monotonie_pour_tout(equivalence_arriere(thm_eq), x)
    return conjonction_intro(avant, arriere)


# @livre Ch.I §4.3 Crit.31 | E I.34 L.20-22 | PDF p.34
def congruence_existe(thm_eq, x):
    """⊢ (R⇔S) (x non libre dans Γ) ⟹ Γ ⊢ (∃x)R ⇔ (∃x)S."""
    avant = monotonie_existe(equivalence_avant(thm_eq), x)
    arriere = monotonie_existe(equivalence_arriere(thm_eq), x)
    return conjonction_intro(avant, arriere)


# @livre Ch.I §4.3 Crit.33 | E I.35 L.8-12 | PDF p.35
def et_existe_droite(p, y, q):
    """⊢ (P et (∃y)Q) ⇔ (∃y)(P et Q)   (y non libre dans P).   (C33, distribution et/∃.)"""
    if y in libres_f(p):
        raise ValueError(f"{y!r} libre dans P")
    h = N.assume(et(p, existe(y, q)))                                      # P et (∃y)Q
    q_imp = N.loi_deduction(q, conjonction_intro(conjonction_elim_gauche(h), N.assume(q)))  # Q⇒(P et Q)
    fwd = N.loi_deduction(et(p, existe(y, q)),
                          N.modus_ponens(conjonction_elim_droite(h), monotonie_existe(q_imp, y)))
    hpq = N.assume(et(p, q))
    conc = conjonction_intro(conjonction_elim_gauche(hpq),
                             N.modus_ponens(conjonction_elim_droite(hpq), N.s5(q, var(y), y)))
    bwd = existe_elimination(N.loi_deduction(et(p, q), conc), y)
    return conjonction_intro(fwd, bwd)


# @livre Ch.I §4.3 Crit.33 | E I.35 L.8-12 | PDF p.35
def et_existe_gauche(y, q, p):
    """⊢ ((∃y)Q et P) ⇔ (∃y)(Q et P)   (y non libre dans P).   (C33, variante gauche.)"""
    if y in libres_f(p):
        raise ValueError(f"{y!r} libre dans P")
    h = N.assume(et(existe(y, q), p))
    q_imp = N.loi_deduction(q, conjonction_intro(N.assume(q), conjonction_elim_droite(h)))  # Q⇒(Q et P)
    fwd = N.loi_deduction(et(existe(y, q), p),
                          N.modus_ponens(conjonction_elim_gauche(h), monotonie_existe(q_imp, y)))
    hqp = N.assume(et(q, p))
    conc = conjonction_intro(N.modus_ponens(conjonction_elim_gauche(hqp), N.s5(q, var(y), y)),
                             conjonction_elim_droite(hqp))
    bwd = existe_elimination(N.loi_deduction(et(q, p), conc), y)
    return conjonction_intro(fwd, bwd)


# @livre Ch.I §4.3 Crit.34 | E I.35 L.21-25 | PDF p.35
def existe_commute(x, y, r):
    """⊢ (∃x)(∃y)R ⇔ (∃y)(∃x)R   (commutation de deux ∃).   (C33.)"""
    def sens(a, b):     # (∃a)(∃b)R ⇒ (∃b)(∃a)R
        r_to = syllogisme(N.s5(r, var(a), a), N.s5(existe(a, r), var(b), b))   # R⇒(∃a)R⇒(∃b)(∃a)R
        return existe_elimination(existe_elimination(r_to, b), a)
    return conjonction_intro(sens(x, y), sens(y, x))


def alpha_existe(x, y, r):
    """⊢ (∃x)R ⇔ (∃y)(y|x)R   (renommage-α du quantificateur ∃ ; y non libre dans R)."""
    if y in libres_f(r):
        raise ValueError(f"renommage-α invalide : {y!r} libre dans R")
    ry = subst_f(var(y), x, r)                          # (y|x)R
    fwd = existe_elimination(N.s5(ry, var(x), y), x)    # (∃x)R ⇒ (∃y)R'   ((x|y)R'=R)
    bwd = existe_elimination(N.s5(r, var(y), x), y)     # (∃y)R' ⇒ (∃x)R   ((y|x)R=R')
    return conjonction_intro(fwd, bwd)


def alpha_pour_tout(x, y, r):
    """⊢ (∀x)R ⇔ (∀y)(y|x)R   (renommage-α du quantificateur ∀ ; y non libre dans R)."""
    if y in libres_f(r):
        raise ValueError(f"renommage-α invalide : {y!r} libre dans R")
    ry = subst_f(var(y), x, r)                          # (y|x)R
    hx = N.assume(pourtout(x, r))
    fwd = N.loi_deduction(pourtout(x, r),
                          N.generalisation(y, N.modus_ponens(hx, instanciation(r, var(y), x))))
    hy = N.assume(pourtout(y, ry))
    bwd = N.loi_deduction(pourtout(y, ry),
                          N.generalisation(x, N.modus_ponens(hy, instanciation(ry, var(x), y))))
    return conjonction_intro(fwd, bwd)


__all__ = ["monotonie_pour_tout", "monotonie_existe", "existe_vacuous",
           "existe_elimination", "congruence_pour_tout", "congruence_existe",
           "et_existe_droite", "et_existe_gauche", "existe_commute",
           "alpha_existe", "alpha_pour_tout"]
