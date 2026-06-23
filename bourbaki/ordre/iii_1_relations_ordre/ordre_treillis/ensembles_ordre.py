"""Chapitre III §1 — Relations d'ordre, ensembles ordonnés : théorèmes DIRECTS.

Tous les résultats sont CERTIFIÉS par le noyau abrégé (type Theoreme opaque).
Une relation R{x,y} est une fonction Python (Terme, Terme) → Formule (cf. §II.6).
Théorèmes :
 - ordre_oppose_est_ordre        : R ordre ⟹ R^op ordre        (§1.1, Exemple 3)
 - preordre_oppose_est_preordre  : R préordre ⟹ R^op préordre  (§1.2)
 - unicite_plus_grand_element    : antisym. ⟹ ≤ 1 plus grand élt (§1.7)
 - unicite_plus_petit_element    : antisym. ⟹ ≤ 1 plus petit élt (§1.7, dual)
 - plus_grand_est_maximal        : plus grand élt ⟹ élt maximal  (§1.6-1.7)
 - plus_petit_est_minimal        : plus petit élt ⟹ élt minimal  (dual)
 - minorant_partie               : a minore X, Y⊂X ⟹ a minore Y  (§1.8)
 - majorant_partie               : a majore X, Y⊂X ⟹ a majore Y  (§1.8, dual)
"""
from __future__ import annotations

from bourbaki.logique.formule import Terme, var, egal, et, appartient, inclus
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles.ii_1_axiomes_algebre import ensembles_abrege as E
from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (instancie, conjonction_intro, conjonction_elim_gauche,
                               conjonction_elim_droite, comm_et, equivalence_avant)
from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie


def _terme(t):
    return t if isinstance(t, Terme) else var(t)


def _inst3(thm_forall3, t1, t2, t3):
    """De Γ⊢(∀a)(∀b)(∀c)P, déduire Γ⊢(t1|a)(t2|b)(t3|c)P."""
    return instancie(instancie(instancie(thm_forall3, t1), t2), t3)


def _inst2(thm_forall2, t1, t2):
    """De Γ⊢(∀a)(∀b)P, déduire Γ⊢(t1|a)(t2|b)P."""
    return instancie(instancie(thm_forall2, t1), t2)


# ── §III.1.1, Exemple 3 — l'ordre opposé est un ordre ─────────────────────────
def ordre_oppose_est_ordre(R, x="x", y="y", z="z"):
    """⊢ est_relation_ordre(R) ⇒ est_relation_ordre(R^op).

    R^op{x,y} := R{y,x}.  Les trois conditions de R^op sont celles de R, à
    permutation près des lettres universellement quantifiées.  (E.III.1.1, Ex. 3.)"""
    Rop = E.ordre_oppose(R)
    vx, vy, vz = var(x), var(y), var(z)
    hyp = E.est_relation_ordre(R, x, y, z)
    H = N.assume(hyp)
    Htr = conjonction_elim_gauche(conjonction_elim_gauche(H))   # ⊢ ordre_transitif(R)
    Has = conjonction_elim_droite(conjonction_elim_gauche(H))   # ⊢ ordre_antisymetrique(R)
    Href = conjonction_elim_droite(H)                            # ⊢ R{x,y}⇒(R{x,x} et R{y,y})

    # (1) transitivité de R^op : (R^op{x,y} et R^op{y,z}) ⇒ R^op{x,z}
    #     = (R{y,x} et R{z,y}) ⇒ R{z,x}.  Instance de Htr en (z, y, x) :
    #     (R{z,y} et R{y,x}) ⇒ R{z,x}.  On précompose par comm_et.
    inst_tr = _inst3(Htr, vz, vy, vx)                           # (R{z,y} et R{y,x}) ⇒ R{z,x}
    comm = comm_et(R(vy, vx), R(vz, vy))                        # (R{y,x} et R{z,y}) ⇔ (R{z,y} et R{y,x})
    op_tr_body = syllogisme(equivalence_avant(comm), inst_tr)   # (R{y,x} et R{z,y}) ⇒ R{z,x}
    op_tr = N.generalisation(x, N.generalisation(y, N.generalisation(z, op_tr_body)))

    # (2) antisymétrie de R^op : (R^op{x,y} et R^op{y,x}) ⇒ x=y
    #     = (R{y,x} et R{x,y}) ⇒ x=y.  Instance de Has en (y, x) : (R{y,x} et R{x,y}) ⇒ y=x.
    #     Puis y=x ⇒ x=y (symétrie de l'égalité) ; mais l'énoncé veut x=y.
    inst_as = _inst2(Has, vy, vx)                              # (R{y,x} et R{x,y}) ⇒ y=x
    op_as_body = syllogisme(inst_as, symetrie(vy, vx))          # (R{y,x} et R{x,y}) ⇒ x=y
    op_as = N.generalisation(x, N.generalisation(y, op_as_body))

    # (3) R^op{x,y} ⇒ (R^op{x,x} et R^op{y,y}) = R{y,x} ⇒ (R{x,x} et R{y,y}).
    #     Instance de Href en (y, x) : R{y,x} ⇒ (R{y,y} et R{x,x}).  Réordonner le et.
    inst_ref = _inst2(Href, vy, vx)                            # R{y,x} ⇒ (R{y,y} et R{x,x})
    swap = equivalence_avant(comm_et(R(vy, vy), R(vx, vx)))     # (R{y,y} et R{x,x}) ⇒ (R{x,x} et R{y,y})
    op_ref_body = syllogisme(inst_ref, swap)                   # R{y,x} ⇒ (R{x,x} et R{y,y})
    op_ref = N.generalisation(x, N.generalisation(y, op_ref_body))

    concl = conjonction_intro(conjonction_intro(op_tr, op_as), op_ref)
    return N.loi_deduction(hyp, concl)


# ── §III.1.2 — le préordre opposé est un préordre ─────────────────────────────
def preordre_oppose_est_preordre(R, x="x", y="y", z="z"):
    """⊢ est_relation_preordre(R) ⇒ est_relation_preordre(R^op).  (E.III.1.2.)"""
    Rop = E.ordre_oppose(R)
    vx, vy, vz = var(x), var(y), var(z)
    hyp = E.est_relation_preordre(R, x, y, z)
    H = N.assume(hyp)
    Htr = conjonction_elim_gauche(H)                            # ordre_transitif(R)
    Href = conjonction_elim_droite(H)                           # R{x,y}⇒(R{x,x} et R{y,y})

    inst_tr = _inst3(Htr, vz, vy, vx)
    comm = comm_et(R(vy, vx), R(vz, vy))
    op_tr_body = syllogisme(equivalence_avant(comm), inst_tr)
    op_tr = N.generalisation(x, N.generalisation(y, N.generalisation(z, op_tr_body)))

    inst_ref = _inst2(Href, vy, vx)
    swap = equivalence_avant(comm_et(R(vy, vy), R(vx, vx)))
    op_ref_body = syllogisme(inst_ref, swap)
    op_ref = N.generalisation(x, N.generalisation(y, op_ref_body))

    return N.loi_deduction(hyp, conjonction_intro(op_tr, op_ref))


# ── §III.1.7 — unicité du plus grand / plus petit élément ─────────────────────
def unicite_plus_grand_element(R, e="E", a="a", b="b", x="x"):
    """{ R antisymétrique, a plus grand élt de E, b plus grand élt de E } ⊢ a=b.

    Bourbaki E.III.1.7 : si a≥x et b≥x pour tout x∈E, alors a≥b et b≥a, d'où a=b
    par antisymétrie."""
    ve, va, vb = _terme(e), _terme(a), _terme(b)
    Has = N.assume(E.ordre_antisymetrique(R, x, "y"))           # (∀x)(∀y)((R{x,y} et R{y,x})⇒x=y)
    Ha = N.assume(E.est_plus_grand_element(R, ve, va, x))       # a∈E et (∀x)(x∈E⇒R{x,a})
    Hb = N.assume(E.est_plus_grand_element(R, ve, vb, x))       # b∈E et (∀x)(x∈E⇒R{x,b})
    a_in = conjonction_elim_gauche(Ha)                          # a∈E
    b_in = conjonction_elim_gauche(Hb)                          # b∈E
    # b≤a : de « a plus grand », instancier en b : b∈E ⇒ R{b,a}
    Ra_b = N.modus_ponens(b_in, instancie(conjonction_elim_droite(Ha), vb))   # R{b,a}
    # a≤b : de « b plus grand », instancier en a : a∈E ⇒ R{a,b}
    Rb_a = N.modus_ponens(a_in, instancie(conjonction_elim_droite(Hb), va))   # R{a,b}
    # antisymétrie en (b, a) : (R{b,a} et R{a,b}) ⇒ b=a, puis symétrie → a=b
    antisym_ba = _inst2(Has, vb, va)                            # (R{b,a} et R{a,b}) ⇒ b=a
    b_eq_a = N.modus_ponens(conjonction_intro(Ra_b, Rb_a), antisym_ba)   # b=a
    return N.modus_ponens(b_eq_a, symetrie(vb, va))             # a=b


def unicite_plus_petit_element(R, e="E", a="a", b="b", x="x"):
    """{ R antisymétrique, a plus petit élt, b plus petit élt } ⊢ a=b.  (E.III.1.7, dual.)"""
    ve, va, vb = _terme(e), _terme(a), _terme(b)
    Has = N.assume(E.ordre_antisymetrique(R, x, "y"))
    Ha = N.assume(E.est_plus_petit_element(R, ve, va, x))       # a∈E et (∀x)(x∈E⇒R{a,x})
    Hb = N.assume(E.est_plus_petit_element(R, ve, vb, x))       # b∈E et (∀x)(x∈E⇒R{b,x})
    a_in = conjonction_elim_gauche(Ha)
    b_in = conjonction_elim_gauche(Hb)
    Ra_b = N.modus_ponens(b_in, instancie(conjonction_elim_droite(Ha), vb))   # R{a,b}
    Rb_a = N.modus_ponens(a_in, instancie(conjonction_elim_droite(Hb), va))   # R{b,a}
    antisym_ab = _inst2(Has, va, vb)                           # (R{a,b} et R{b,a}) ⇒ a=b
    return N.modus_ponens(conjonction_intro(Ra_b, Rb_a), antisym_ab)   # a=b


# ── §III.1.6-1.7 — plus grand ⟹ maximal, plus petit ⟹ minimal ────────────────
def plus_grand_est_maximal(R, e="E", a="a", x="x"):
    """{ R antisymétrique, a plus grand élt de E } ⊢ a élément maximal de E.

    a maximal := a∈E et (∀x)((x∈E et R{a,x})⇒x=a).  Si a est plus grand, R{x,a}
    pour tout x∈E ; et si R{a,x}, l'antisymétrie donne x=a.  (E.III.1.6-1.7.)"""
    ve, va, vx = _terme(e), _terme(a), var(x)
    Has = N.assume(E.ordre_antisymetrique(R, x, "y"))
    Ha = N.assume(E.est_plus_grand_element(R, ve, va, x))       # a∈E et (∀x)(x∈E⇒R{x,a})
    a_in = conjonction_elim_gauche(Ha)
    grand = conjonction_elim_droite(Ha)                         # (∀x)(x∈E⇒R{x,a})
    # corps : (x∈E et R{a,x}) ⇒ x=a
    hyp_body = et(appartient(vx, ve), R(va, vx))
    Hbody = N.assume(hyp_body)
    x_in = conjonction_elim_gauche(Hbody)                      # x∈E
    Rax = conjonction_elim_droite(Hbody)                       # R{a,x}
    Rxa = N.modus_ponens(x_in, instancie(grand, vx))           # R{x,a}
    antisym_xa = _inst2(Has, vx, va)                           # (R{x,a} et R{a,x})⇒x=a
    x_eq_a = N.modus_ponens(conjonction_intro(Rxa, Rax), antisym_xa)   # x=a
    body = N.loi_deduction(hyp_body, x_eq_a)                    # (x∈E et R{a,x})⇒x=a
    return conjonction_intro(a_in, N.generalisation(x, body))


def plus_petit_est_minimal(R, e="E", a="a", x="x"):
    """{ R antisymétrique, a plus petit élt de E } ⊢ a élément minimal de E.  (dual.)"""
    ve, va, vx = _terme(e), _terme(a), var(x)
    Has = N.assume(E.ordre_antisymetrique(R, x, "y"))
    Ha = N.assume(E.est_plus_petit_element(R, ve, va, x))       # a∈E et (∀x)(x∈E⇒R{a,x})
    a_in = conjonction_elim_gauche(Ha)
    petit = conjonction_elim_droite(Ha)                        # (∀x)(x∈E⇒R{a,x})
    hyp_body = et(appartient(vx, ve), R(vx, va))               # (x∈E et R{x,a})
    Hbody = N.assume(hyp_body)
    x_in = conjonction_elim_gauche(Hbody)
    Rxa = conjonction_elim_droite(Hbody)                       # R{x,a}
    Rax = N.modus_ponens(x_in, instancie(petit, vx))           # R{a,x}
    antisym_xa = _inst2(Has, vx, va)                           # (R{x,a} et R{a,x})⇒x=a
    x_eq_a = N.modus_ponens(conjonction_intro(Rxa, Rax), antisym_xa)   # x=a
    body = N.loi_deduction(hyp_body, x_eq_a)
    return conjonction_intro(a_in, N.generalisation(x, body))


# ── §III.1.8 — un minorant de X minore toute partie de X ──────────────────────
def minorant_partie(R, X="X", Y="Y", a="a", y="y"):
    """{ a minore X, Y⊂X } ⊢ a minore Y.   (« un minorant de X est aussi minorant de
    toute partie de X », E.III.1.8.)"""
    vX, vY, va, vy = _terme(X), _terme(Y), _terme(a), var(y)
    Hmin = N.assume(E.minore(R, vX, va, y))                    # (∀y)(y∈X⇒R{a,y})
    Hsub = N.assume(inclus(vY, vX))                            # Y⊂X
    Hb = N.assume(appartient(vy, vY))                          # y∈Y
    # Y⊂X = (∀z)(z∈Y⇒z∈X) ; instancier en y
    y_in_X = N.modus_ponens(Hb, _inst_inclus(Hsub, vy))        # y∈X
    Ray = N.modus_ponens(y_in_X, instancie(Hmin, vy))          # R{a,y}
    body = N.loi_deduction(appartient(vy, vY), Ray)            # y∈Y ⇒ R{a,y}
    return N.generalisation(y, body)                           # (∀y)(y∈Y⇒R{a,y}) = a minore Y


def majorant_partie(R, X="X", Y="Y", a="a", y="y"):
    """{ a majore X, Y⊂X } ⊢ a majore Y.   (E.III.1.8, dual.)"""
    vX, vY, va, vy = _terme(X), _terme(Y), _terme(a), var(y)
    Hmaj = N.assume(E.majore(R, vX, va, y))                    # (∀y)(y∈X⇒R{y,a})
    Hsub = N.assume(inclus(vY, vX))                            # Y⊂X
    Hb = N.assume(appartient(vy, vY))
    y_in_X = N.modus_ponens(Hb, _inst_inclus(Hsub, vy))        # y∈X
    Rya = N.modus_ponens(y_in_X, instancie(Hmaj, vy))          # R{y,a}
    body = N.loi_deduction(appartient(vy, vY), Rya)
    return N.generalisation(y, body)


def _inst_inclus(thm_sub, t):
    """De Γ⊢(Y⊂X) = (∀z)(z∈Y⇒z∈X), déduire Γ⊢(t∈Y⇒t∈X)."""
    return instancie(thm_sub, t)


__all__ = ["ordre_oppose_est_ordre", "preordre_oppose_est_preordre",
           "unicite_plus_grand_element", "unicite_plus_petit_element",
           "plus_grand_est_maximal", "plus_petit_est_minimal",
           "minorant_partie", "majorant_partie"]
