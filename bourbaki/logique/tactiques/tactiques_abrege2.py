"""Boîte à outils abrégée (portée du niveau τ) + ⊂-transitivité (chap. II).

Comme ⇒ = ¬∨ au niveau abrégé, les dérivations sont IDENTIQUES à tactiques.py /
tactiques_prop.py / tactiques_egalite.py — on les porte sur `noyau_abrege`.
"""
from __future__ import annotations

from bourbaki.logique.formule import (var, non, ou, et, egal, impl, existe, pourtout, appartient,
                     inclus, subst_f)
from bourbaki.logique import noyau_abrege as N
from bourbaki.logique.tactiques.tactiques_abrege import antecedent_consequent, a_implique_a, syllogisme


# ── monotonie de ∨, affaiblissement ───────────────────────────────────────────
def mono_droite(thm_pq, c):
    p, q = antecedent_consequent(thm_pq.conclusion)
    return N.modus_ponens(thm_pq, N.s4(p, q, c))


def mono_gauche(thm_pq, c):
    p, q = antecedent_consequent(thm_pq.conclusion)
    return syllogisme(syllogisme(N.s3(p, c), mono_droite(thm_pq, c)), N.s3(c, q))


def affaiblissement(thm, a):
    x = thm.conclusion
    return N.modus_ponens(N.modus_ponens(thm, N.s2(x, non(a))), N.s3(x, non(a)))


# ── double négation, contraposition ───────────────────────────────────────────
def dni(a):
    return N.modus_ponens(a_implique_a(non(a)), N.s3(non(non(a)), non(a)))


def dne(a):
    return N.modus_ponens(a_implique_a(a), mono_gauche(dni(non(a)), a))


def contraposition(thm_pq):
    p, q = antecedent_consequent(thm_pq.conclusion)
    comm = N.modus_ponens(thm_pq, N.s3(non(p), q))
    return N.modus_ponens(comm, mono_gauche(dni(q), non(p)))


def distribution(t_a_bc, t_ab):
    a, _ = antecedent_consequent(t_ab.conclusion)
    h = N.assume(a)
    hc = N.modus_ponens(N.modus_ponens(h, t_ab), N.modus_ponens(h, t_a_bc))
    return N.loi_deduction(a, hc)


def disj_syll_thm(p, q):
    return mono_gauche(dni(p), q)


# ── conjonction (intro + élim) ────────────────────────────────────────────────
def conjonction_intro(ta, tb):
    a, b = ta.conclusion, tb.conclusion
    nnA = N.modus_ponens(ta, dni(a))
    nnB = N.modus_ponens(tb, dni(b))
    h = ou(non(a), non(b))
    h_nb = distribution(disj_syll_thm(non(a), non(b)), affaiblissement(nnA, h))
    return N.modus_ponens(nnB, contraposition(h_nb))


def composantes_conjonction(c):
    if not (c.tag == "non" and c.sous[0].tag == "ou"):
        raise ValueError("pas une conjonction ¬(¬A∨¬B)")
    g, d = c.sous[0].sous
    if not (g.tag == "non" and d.tag == "non"):
        raise ValueError("pas une conjonction")
    return g.sous[0], d.sous[0]


def projection_gauche(a, b):
    return syllogisme(contraposition(N.s2(non(a), non(b))), dne(a))


def projection_droite(a, b):
    t = syllogisme(N.s2(non(b), non(a)), N.s3(non(b), non(a)))
    return syllogisme(contraposition(t), dne(b))


def conjonction_elim_gauche(thm):
    a, b = composantes_conjonction(thm.conclusion)
    return N.modus_ponens(thm, projection_gauche(a, b))


def conjonction_elim_droite(thm):
    a, b = composantes_conjonction(thm.conclusion)
    return N.modus_ponens(thm, projection_droite(a, b))


# ── ∀-élimination (C30, cas T = x) ────────────────────────────────────────────
def instanciation_en_x(r, x):
    """⊢ (∀x)R ⇒ R."""
    s5 = N.s5(non(r), var(x), x)                       # ⊢ ¬R ⇒ (∃x)¬R
    return syllogisme(contraposition(s5), dne(r))      # ⊢ (∀x)R ⇒ R


def comm_ou(p, q):
    """⊢ (P ∨ Q) ⇔ (Q ∨ P)."""
    return conjonction_intro(N.s3(p, q), N.s3(q, p))


def tiers_exclu(p):
    """⊢ P ∨ ¬P  (principe du tiers exclu)."""
    return N.modus_ponens(a_implique_a(p), N.s3(non(p), p))   # (¬P∨P) → (P∨¬P)


def comm_et(p, q):
    """⊢ (P et Q) ⇔ (Q et P)."""
    def sens(x, y):
        h = N.assume(et(x, y))
        swap = conjonction_intro(conjonction_elim_droite(h), conjonction_elim_gauche(h))
        return N.loi_deduction(et(x, y), swap)
    return conjonction_intro(sens(p, q), sens(q, p))


def ou_congruence(thm_a, thm_b):
    """⊢ (A⇔A'), ⊢ (B⇔B') ⟹ ⊢ (A∨B) ⇔ (A'∨B')."""
    a, ap = antecedent_consequent(conjonction_elim_gauche(thm_a).conclusion)
    b, bp = antecedent_consequent(conjonction_elim_gauche(thm_b).conclusion)
    fwd = syllogisme(mono_gauche(conjonction_elim_gauche(thm_a), b),
                     mono_droite(conjonction_elim_gauche(thm_b), ap))      # (A∨B)⇒(A'∨B')
    bwd = syllogisme(mono_gauche(conjonction_elim_droite(thm_a), bp),
                     mono_droite(conjonction_elim_droite(thm_b), a))       # (A'∨B')⇒(A∨B)
    return conjonction_intro(fwd, bwd)


def equiv_neg(thm_pq):
    """⊢ (P⇔Q) ⟹ ⊢ (¬P ⇔ ¬Q)  (congruence de la négation)."""
    return conjonction_intro(contraposition(conjonction_elim_droite(thm_pq)),
                             contraposition(conjonction_elim_gauche(thm_pq)))


def demorgan_ou(p, q):
    """⊢ ¬(P∨Q) ⇔ (¬P et ¬Q).   (loi de De Morgan ; et(¬P,¬Q)=¬(¬¬P∨¬¬Q).)"""
    dnP = conjonction_intro(dne(p), dni(p))            # ¬¬P ⇔ P
    dnQ = conjonction_intro(dne(q), dni(q))            # ¬¬Q ⇔ Q
    eq = equiv_neg(ou_congruence(dnP, dnQ))            # ¬(¬¬P∨¬¬Q) ⇔ ¬(P∨Q)  = (¬P et ¬Q) ⇔ ¬(P∨Q)
    return conjonction_intro(conjonction_elim_droite(eq), conjonction_elim_gauche(eq))  # symétrisé


def demorgan_et(p, q):
    """⊢ ¬(P et Q) ⇔ (¬P ∨ ¬Q).   (¬(P et Q) = ¬¬(¬P∨¬Q).)"""
    x = ou(non(p), non(q))
    return conjonction_intro(dne(x), dni(x))           # ¬¬X ⇔ X  = ¬(P et Q) ⇔ (¬P∨¬Q)


def et_ou_distrib(p, q, r):
    """⊢ (P et (Q∨R)) ⇔ ((P et Q) ∨ (P et R))   (distribution de et sur ∨)."""
    h = N.assume(et(p, ou(q, r)))
    pp = conjonction_elim_gauche(h)
    brQ = N.loi_deduction(q, N.modus_ponens(conjonction_intro(pp, N.assume(q)),
                                            N.s2(et(p, q), et(p, r))))
    brR = N.loi_deduction(r, N.modus_ponens(N.modus_ponens(conjonction_intro(pp, N.assume(r)),
                          N.s2(et(p, r), et(p, q))), N.s3(et(p, r), et(p, q))))
    fwd = N.loi_deduction(et(p, ou(q, r)), cas(conjonction_elim_droite(h), brQ, brR))
    h2 = N.assume(ou(et(p, q), et(p, r)))
    hpq = N.assume(et(p, q))
    brPQ = N.loi_deduction(et(p, q), conjonction_intro(conjonction_elim_gauche(hpq),
                           N.modus_ponens(conjonction_elim_droite(hpq), N.s2(q, r))))
    hpr = N.assume(et(p, r))
    brPR = N.loi_deduction(et(p, r), conjonction_intro(conjonction_elim_gauche(hpr),
                           N.modus_ponens(N.modus_ponens(conjonction_elim_droite(hpr), N.s2(r, q)),
                                          N.s3(r, q))))
    bwd = N.loi_deduction(ou(et(p, q), et(p, r)), cas(h2, brPQ, brPR))
    return conjonction_intro(fwd, bwd)


def assoc_et(p, q, r):
    """⊢ (P et (Q et R)) ⇔ ((P et Q) et R)."""
    h1 = N.assume(et(p, et(q, r)))
    qr = conjonction_elim_droite(h1)
    fwd = N.loi_deduction(et(p, et(q, r)), conjonction_intro(
        conjonction_intro(conjonction_elim_gauche(h1), conjonction_elim_gauche(qr)),
        conjonction_elim_droite(qr)))
    h2 = N.assume(et(et(p, q), r))
    pq = conjonction_elim_gauche(h2)
    bwd = N.loi_deduction(et(et(p, q), r), conjonction_intro(
        conjonction_elim_gauche(pq),
        conjonction_intro(conjonction_elim_droite(pq), conjonction_elim_droite(h2))))
    return conjonction_intro(fwd, bwd)


def cas(thm_disj, thm_ac, thm_bc):
    """Γ⊢(A∨B), Δ⊢(A⇒C), Θ⊢(B⇒C) ⟹ Γ∪Δ∪Θ ⊢ C.  (élimination de ∨, preuve par cas.)"""
    a, b = thm_disj.conclusion.sous
    _, c = antecedent_consequent(thm_ac.conclusion)
    etape1 = mono_gauche(thm_ac, b)                    # (A∨B) ⇒ (C∨B)
    etape2 = mono_droite(thm_bc, c)                    # (C∨B) ⇒ (C∨C)
    chaine = syllogisme(syllogisme(etape1, etape2), N.s1(c))   # (A∨B) ⇒ C
    return N.modus_ponens(thm_disj, chaine)


def et_congruence_droite(p, thm_eq):
    """⊢ (Q⇔Q') ⟹ ⊢ (P et Q) ⇔ (P et Q').   (congruence du et, conjonct droit.)"""
    q, qp = antecedent_consequent(equivalence_avant(thm_eq).conclusion)
    hf = N.assume(et(p, q))
    fwd = N.loi_deduction(et(p, q), conjonction_intro(
        conjonction_elim_gauche(hf), N.modus_ponens(conjonction_elim_droite(hf), equivalence_avant(thm_eq))))
    hb = N.assume(et(p, qp))
    bwd = N.loi_deduction(et(p, qp), conjonction_intro(
        conjonction_elim_gauche(hb), N.modus_ponens(conjonction_elim_droite(hb), equivalence_arriere(thm_eq))))
    return conjonction_intro(fwd, bwd)


def et_congruence_gauche(thm_eq, p):
    """⊢ (Q⇔Q') ⟹ ⊢ (Q et P) ⇔ (Q' et P).   (congruence du et, conjonct gauche.)"""
    q, qp = antecedent_consequent(equivalence_avant(thm_eq).conclusion)
    hf = N.assume(et(q, p))
    fwd = N.loi_deduction(et(q, p), conjonction_intro(
        N.modus_ponens(conjonction_elim_gauche(hf), equivalence_avant(thm_eq)), conjonction_elim_droite(hf)))
    hb = N.assume(et(qp, p))
    bwd = N.loi_deduction(et(qp, p), conjonction_intro(
        N.modus_ponens(conjonction_elim_gauche(hb), equivalence_arriere(thm_eq)), conjonction_elim_droite(hb)))
    return conjonction_intro(fwd, bwd)


def equivalence_avant(thm_eq):
    """Γ ⊢ (A⇔B) ⟹ Γ ⊢ (A⇒B)."""
    return conjonction_elim_gauche(thm_eq)


def equivalence_arriere(thm_eq):
    """Γ ⊢ (A⇔B) ⟹ Γ ⊢ (B⇒A)."""
    return conjonction_elim_droite(thm_eq)


def equivalence_symetrie(thm_eq):
    """Γ ⊢ (A⇔B) ⟹ Γ ⊢ (B⇔A)."""
    return conjonction_intro(equivalence_arriere(thm_eq), equivalence_avant(thm_eq))


def equivalence_transitivite(thm_ab, thm_bc):
    """⊢ (A⇔B), ⊢ (B⇔C) ⟹ ⊢ (A⇔C)."""
    ac = syllogisme(equivalence_avant(thm_ab), equivalence_avant(thm_bc))
    ca = syllogisme(equivalence_arriere(thm_bc), equivalence_arriere(thm_ab))
    return conjonction_intro(ac, ca)


def instanciation(r, t, x):
    """⊢ (∀x)R ⇒ (T|x)R.  C30 général (terme T quelconque)."""
    s5 = N.s5(non(r), t, x)                            # ⊢ (T|x)¬R ⇒ (∃x)¬R
    return syllogisme(contraposition(s5), dne(subst_f(t, x, r)))  # ⊢ (∀x)R ⇒ (T|x)R


def _peler_pourtout(f):
    """(∀x)R = ¬(∃x)¬R → (x, R)."""
    if not (f.tag == "non" and f.sous[0].tag == "exists" and f.sous[0].sous[0].tag == "non"):
        raise ValueError("pas un (∀x)R")
    return f.sous[0].lieur, f.sous[0].sous[0].sous[0]


def instancie(thm_forall, t):
    """Γ ⊢ (∀x)R  ⟹  Γ ⊢ (T|x)R.  (∀-élimination à un terme T.)"""
    x, r = _peler_pourtout(thm_forall.conclusion)
    return N.modus_ponens(thm_forall, instanciation(r, t, x))


# ── Chapitre II — transitivité de l'inclusion ─────────────────────────────────
def inclusion_transitive(a="a", b="b", c="c"):
    """⊢ ((a ⊂ b) et (b ⊂ c)) ⇒ (a ⊂ c)."""
    va, vb, vc, z = var(a), var(b), var(c), "z"
    zt = var(z)
    hyp = et(inclus(va, vb), inclus(vb, vc))            # (a⊂b) et (b⊂c)
    h = N.assume(hyp)
    rab = impl(appartient(zt, va), appartient(zt, vb))
    rbc = impl(appartient(zt, vb), appartient(zt, vc))
    zab = N.modus_ponens(conjonction_elim_gauche(h), instanciation_en_x(rab, z))
    zbc = N.modus_ponens(conjonction_elim_droite(h), instanciation_en_x(rbc, z))
    gen = N.generalisation(z, syllogisme(zab, zbc))     # {H} ⊢ (∀z)(z∈a⇒z∈c)
    return N.loi_deduction(hyp, gen)                    # ⊢ ((a⊂b) et (b⊂c)) ⇒ (a⊂c)


__all__ = ["mono_droite", "mono_gauche", "affaiblissement", "dni", "dne",
           "contraposition", "distribution", "disj_syll_thm", "conjonction_intro",
           "composantes_conjonction", "projection_gauche", "projection_droite",
           "conjonction_elim_gauche", "conjonction_elim_droite",
           "comm_ou", "comm_et", "assoc_et", "ou_congruence", "equiv_neg", "demorgan_ou",
           "demorgan_et", "et_ou_distrib", "cas", "tiers_exclu",
           "et_congruence_droite", "et_congruence_gauche",
           "equivalence_avant", "equivalence_arriere", "equivalence_symetrie",
           "equivalence_transitivite",
           "instanciation_en_x", "instanciation", "instancie", "inclusion_transitive"]
