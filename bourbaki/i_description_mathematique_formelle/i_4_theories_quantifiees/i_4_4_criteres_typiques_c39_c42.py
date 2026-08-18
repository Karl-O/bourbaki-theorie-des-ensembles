"""Critères des quantificateurs TYPIQUES C39, C40, C42 (Bourbaki §I.4.4, E I.37).

Quantificateurs typiques (relativisés à une relation A) — définitions de Bourbaki :
    (∃_A x)R := (∃x)(A et R)            →  `existe_typique`
    (∀_A x)R := ¬(∃x)(A et ¬R)         →  `pourtout_typique`
Ces définitions sont EXACTEMENT les nœuds construits ici ; l'égalité des conclusions
avec les cibles est donc structurelle (`==`), pas seulement à α-près.

Les trois critères (cf. E I.37) :
  • C39 — sous l'hypothèse A⇒(R⇒S) :  (∃_A x)R ⇒ (∃_A x)S   et   (∀_A x)R ⇒ (∀_A x)S.
  • C40 — théorèmes purs :  (∀_A x)(R et S) ⇔ ((∀_A x)R et (∀_A x)S)
                            et  (∃_A x)(R ou S) ⇔ ((∃_A x)R ou (∃_A x)S).
  • C42 — commutation (x∉B, y∉A) :  (∀_A x)(∀_B y)R ⇔ (∀_B y)(∀_A x)R
                                    et  (∃_A x)(∃_B y)R ⇔ (∃_B y)(∃_A x)R.

STRATÉGIE (tout dérivé des primitives N.* via les tactiques déjà certifiées) :
  C39 : de A⇒(R⇒S) on construit (A et R)⇒(A et S) [resp. (A et ¬S)⇒(A et ¬R) par
        contraposition interne], puis `monotonie_existe` ; le sens ∀ se referme par
        `contraposition` de l'implication ∃ duale.
  C40 : congruence propositionnelle (`et_ou_distrib`, distribution de ⇒ sur et) sous
        `congruence_existe`/`congruence_pour_tout`, puis distribution plain ∃/ou et
        ∀/et, chaînée par `equivalence_transitivite`. Le cas ∀ passe par C35 local
        ((∀_A x)F ⇔ (∀x)(A⇒F)).
  C42 : le cas ∃∃ fait passer A,B à travers les ∃ via `et_existe_droite` (fraîcheur
        x∉B, y∉A) puis échange par `existe_commute`. Le cas ∀∀ se RAMÈNE au cas ∃∃
        sur ¬R par la dualité (∀_A x)F = ¬(∃_A x)¬F (collapse des ¬¬ + `equiv_neg`).

INVARIANTS : C39 garde exactement {A⇒(R⇒S)} en hypothèse (conclusion ∉ hypothèses) ;
C40 et C42 sont CLOS (0 hypothèse) — aucune tautologie déguisée. theorie == 22.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (var, non, et, ou, impl, equiv,
                     existe, pourtout, libres_f)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import antecedent_consequent, syllogisme
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite, contraposition,
    et_ou_distrib, cas, equivalence_avant, equivalence_symetrie, equivalence_transitivite,
    projection_gauche, projection_droite, instanciation_en_x, et_congruence_gauche,
    et_congruence_droite, demorgan_ou, dne, dni, equiv_neg)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    monotonie_existe, congruence_existe, congruence_pour_tout, existe_commute,
    et_existe_droite, existe_elimination)


# ── Quantificateurs typiques (définitions Bourbaki, E I.37) ───────────────────
def existe_typique(a, x, r):
    """(∃_A x)R := (∃x)(A et R)."""
    return existe(x, et(a, r))


def pourtout_typique(a, x, r):
    """(∀_A x)R := ¬(∃x)(A et ¬R)  (= ¬(∃_A x)¬R)."""
    return non(existe(x, et(a, non(r))))


# ── Lemmes de distribution « plain » (quantificateurs ordinaires) ─────────────
def _existe_ou_distrib(p, x, q):
    """⊢ (∃x)(P ou Q) ⇔ ((∃x)P ou (∃x)Q)  (distribution de ∃ sur ou)."""
    ep, eq = existe(x, p), existe(x, q)
    p_to = syllogisme(N.s5(p, var(x), x), N.s2(ep, eq))                      # P ⇒ (ep ou eq)
    q_to = syllogisme(N.s5(q, var(x), x), syllogisme(N.s2(eq, ep), N.s3(eq, ep)))  # Q ⇒ (ep ou eq)
    rhs = cas(N.assume(ou(p, q)), p_to, q_to)
    fwd = existe_elimination(N.loi_deduction(ou(p, q), rhs), x)              # (∃x)(P ou Q) ⇒ (ep ou eq)
    ep_to = monotonie_existe(N.s2(p, q), x)                                  # ep ⇒ (∃x)(P ou Q)
    eq_to = monotonie_existe(syllogisme(N.s2(q, p), N.s3(q, p)), x)          # eq ⇒ (∃x)(P ou Q)
    bwd = N.loi_deduction(ou(ep, eq), cas(N.assume(ou(ep, eq)), ep_to, eq_to))
    return conjonction_intro(fwd, bwd)


def _pourtout_et_distrib(p, x, q):
    """⊢ (∀x)(P et Q) ⇔ ((∀x)P et (∀x)Q)  (distribution de ∀ sur et)."""
    pp, qq = pourtout(x, p), pourtout(x, q)
    h = N.assume(pourtout(x, et(p, q)))
    pq = N.modus_ponens(h, instanciation_en_x(et(p, q), x))
    fwd = N.loi_deduction(pourtout(x, et(p, q)), conjonction_intro(
        N.generalisation(x, conjonction_elim_gauche(pq)),
        N.generalisation(x, conjonction_elim_droite(pq))))
    h2 = N.assume(et(pp, qq))
    pr = N.modus_ponens(conjonction_elim_gauche(h2), instanciation_en_x(p, x))
    qr = N.modus_ponens(conjonction_elim_droite(h2), instanciation_en_x(q, x))
    bwd = N.loi_deduction(et(pp, qq), N.generalisation(x, conjonction_intro(pr, qr)))
    return conjonction_intro(fwd, bwd)


def _congruence_et(eq1, eq2):
    """⊢ (P⇔P'), (Q⇔Q') ⟹ ⊢ (P et Q) ⇔ (P' et Q')."""
    _, pp = antecedent_consequent(equivalence_avant(eq1).conclusion)
    q, _ = antecedent_consequent(equivalence_avant(eq2).conclusion)
    return equivalence_transitivite(et_congruence_gauche(eq1, q),
                                    et_congruence_droite(pp, eq2))


# ── C35 local et distributions propositionnelles ─────────────────────────────
def _c35(a, f, x):
    """⊢ (∀_A x)F ⇔ (∀x)(A⇒F).   ((A et ¬F) ⇔ ¬(A⇒F) sous ∃, puis négation.)"""
    eq = equivalence_symetrie(equivalence_transitivite(
        demorgan_ou(non(a), f),                                  # ¬(A⇒F) ⇔ (¬¬A et ¬F)
        et_congruence_gauche(conjonction_intro(dne(a), dni(a)), non(f))))  # (¬¬A et ¬F)⇔(A et ¬F)
    return equiv_neg(congruence_existe(eq, x))                  # ¬(∃x)(A et ¬F) ⇔ ¬(∃x)¬(A⇒F)


def _impl_et_distrib(a, r, s):
    """⊢ (A⇒(R et S)) ⇔ ((A⇒R) et (A⇒S))."""
    h = N.assume(impl(a, et(r, s)))
    fwd = N.loi_deduction(impl(a, et(r, s)), conjonction_intro(
        syllogisme(h, projection_gauche(r, s)), syllogisme(h, projection_droite(r, s))))
    h2 = N.assume(et(impl(a, r), impl(a, s)))
    ha = N.assume(a)
    rs = conjonction_intro(N.modus_ponens(ha, conjonction_elim_gauche(h2)),
                           N.modus_ponens(ha, conjonction_elim_droite(h2)))
    bwd = N.loi_deduction(et(impl(a, r), impl(a, s)), N.loi_deduction(a, rs))
    return conjonction_intro(fwd, bwd)


# ── C39 — monotonie typique sous hypothèse A⇒(R⇒S) ───────────────────────────
# @livre Ch.I §4.4 Crit.39 | E I.37 L.18-26 | PDF p.37
# @livre Ch.I §4.4 Demo.- | E I.37 L.27-27 | PDF p.37  (démo de C39, une ligne)
def c39_existe_typique(a, r, s, x):
    """{A⇒(R⇒S)} ⊢ (∃_A x)R ⇒ (∃_A x)S.   (x non libre dans A,R,S.)

    De A⇒(R⇒S) : (A et R)⇒(A et S) (assume/élim/MP/intro/déduction), puis
    `monotonie_existe`. L'hypothèse A⇒(R⇒S) est la SEULE non déchargée."""
    h = N.assume(impl(a, impl(r, s)))
    har = N.assume(et(a, r))
    aa = conjonction_elim_gauche(har)
    ss = N.modus_ponens(conjonction_elim_droite(har), N.modus_ponens(aa, h))   # S
    inner = N.loi_deduction(et(a, r), conjonction_intro(aa, ss))               # (A et R)⇒(A et S)
    return monotonie_existe(inner, x)


# @livre Ch.I §4.4 Crit.39 | E I.37 L.18-26 | PDF p.37
def c39_pourtout_typique(a, r, s, x):
    """{A⇒(R⇒S)} ⊢ (∀_A x)R ⇒ (∀_A x)S.   (x non libre dans A,R,S.)

    Contraposition interne : (A et ¬S)⇒(A et ¬R), `monotonie_existe`, puis
    `contraposition` donne ¬(∃x)(A et ¬R) ⇒ ¬(∃x)(A et ¬S) = (∀_A x)R ⇒ (∀_A x)S."""
    h = N.assume(impl(a, impl(r, s)))
    hans = N.assume(et(a, non(s)))
    aa = conjonction_elim_gauche(hans)
    nrr = N.modus_ponens(conjonction_elim_droite(hans), contraposition(N.modus_ponens(aa, h)))  # ¬R
    inner = N.loi_deduction(et(a, non(s)), conjonction_intro(aa, nrr))         # (A et ¬S)⇒(A et ¬R)
    return contraposition(monotonie_existe(inner, x))


# ── C40 — distribution typique (théorèmes purs) ──────────────────────────────
# @livre Ch.I §4.4 Crit.40 | E I.37 L.28-33 | PDF p.37
# @livre Ch.I §4.4 Demo.- | E I.37 L.34-34 | PDF p.37  (démo de C40, une ligne)
def c40_existe_typique(a, r, s, x):
    """⊢ (∃_A x)(R ou S) ⇔ ((∃_A x)R ou (∃_A x)S).

    (A et (R ou S)) ⇔ ((A et R) ou (A et S)) [et_ou_distrib] sous `congruence_existe`,
    puis distribution plain ∃/ou."""
    return equivalence_transitivite(
        congruence_existe(et_ou_distrib(a, r, s), x),
        _existe_ou_distrib(et(a, r), x, et(a, s)))


# @livre Ch.I §4.4 Crit.40 | E I.37 L.28-33 | PDF p.37
def c40_pourtout_typique(a, r, s, x):
    """⊢ (∀_A x)(R et S) ⇔ ((∀_A x)R et (∀_A x)S).

    Via C35 : (∀_A x)(R et S) ⇔ (∀x)(A⇒(R et S)) ⇔ (∀x)((A⇒R) et (A⇒S))
    ⇔ ((∀x)(A⇒R) et (∀x)(A⇒S)) ⇔ ((∀_A x)R et (∀_A x)S)."""
    e1 = _c35(a, et(r, s), x)
    e2 = congruence_pour_tout(_impl_et_distrib(a, r, s), x)
    e3 = _pourtout_et_distrib(impl(a, r), x, impl(a, s))
    e4 = _congruence_et(equivalence_symetrie(_c35(a, r, x)),
                        equivalence_symetrie(_c35(a, s, x)))
    return equivalence_transitivite(
        equivalence_transitivite(equivalence_transitivite(e1, e2), e3), e4)


# ── C42 — commutation typique (conditions de fraîcheur x∉B, y∉A) ─────────────
def _et_reassoc(a, b, r):
    """⊢ (A et (B et R)) ⇔ (B et (A et R))."""
    h = N.assume(et(a, et(b, r)))
    aa, br = conjonction_elim_gauche(h), conjonction_elim_droite(h)
    fwd = N.loi_deduction(et(a, et(b, r)), conjonction_intro(
        conjonction_elim_gauche(br), conjonction_intro(aa, conjonction_elim_droite(br))))
    h2 = N.assume(et(b, et(a, r)))
    bb, ar = conjonction_elim_gauche(h2), conjonction_elim_droite(h2)
    bwd = N.loi_deduction(et(b, et(a, r)), conjonction_intro(
        conjonction_elim_gauche(ar), conjonction_intro(bb, conjonction_elim_droite(ar))))
    return conjonction_intro(fwd, bwd)


# @livre Ch.I §4.4 Crit.42 | E I.37 L.35-41 | PDF p.37
# @livre Ch.I §4.4 Demo.- | E I.37 L.42-42 | PDF p.37  (démo de C42, une ligne)
# @livre Ch.I §4.4 Demo.- | E I.38 L.1-5 | PDF p.38  (démonstration d'une partie de C42, via C33+C31+C34)
# @livre Ch.I §4.4 Ex.- | E I.38 L.6-13 | PDF p.38  (exemple en petit texte : négation de « (fₙ) converge uniformément vers 0 » via C38 — prose, rien à formaliser)
def c42_existe_typique(a, b, r, x, y):
    """⊢ (∃_A x)(∃_B y)R ⇔ (∃_B y)(∃_A x)R   (x∉B, y∉A).

    Pull de A à travers ∃y et de B à travers ∃x (`et_existe_droite`, fraîcheur),
    échange des deux ∃ (`existe_commute`), réassociation des conjonctions."""
    if x in libres_f(b) or y in libres_f(a):
        raise ValueError("C42 : conditions de fraîcheur (x∉B, y∉A) violées")
    e1 = congruence_existe(et_existe_droite(a, y, et(b, r)), x)   # ⇔ (∃x)(∃y)(A et (B et R))
    e2 = existe_commute(x, y, et(a, et(b, r)))                    # ⇔ (∃y)(∃x)(A et (B et R))
    e3 = congruence_existe(congruence_existe(_et_reassoc(a, b, r), x), y)  # ⇔ (∃y)(∃x)(B et (A et R))
    e4 = congruence_existe(equivalence_symetrie(et_existe_droite(b, x, et(a, r))), y)  # ⇔ (∃_B y)(∃_A x)R
    return equivalence_transitivite(
        equivalence_transitivite(equivalence_transitivite(e1, e2), e3), e4)


def _collapse_dn_typique(a, x, g):
    """⊢ (∃x)(A et ¬¬G) ⇔ (∃x)(A et G)  (collapse du ¬¬ sous le ∃ typique)."""
    return congruence_existe(et_congruence_droite(a, conjonction_intro(dne(g), dni(g))), x)


# @livre Ch.I §4.4 Crit.42 | E I.37 L.35-41 | PDF p.37
def c42_pourtout_typique(a, b, r, x, y):
    """⊢ (∀_A x)(∀_B y)R ⇔ (∀_B y)(∀_A x)R   (x∉B, y∉A).

    Dualité (∀_A x)F = ¬(∃_A x)¬F : on collapse les ¬¬ parasites sous le ∃ externe,
    puis `equiv_neg` du cas ∃∃ (C42) appliqué à ¬R."""
    if x in libres_f(b) or y in libres_f(a):
        raise ValueError("C42 : conditions de fraîcheur (x∉B, y∉A) violées")
    eqL = equiv_neg(_collapse_dn_typique(a, x, existe(y, et(b, non(r)))))     # ⇔ ¬(∃_A x)(∃_B y)¬R
    mid = equiv_neg(c42_existe_typique(a, b, non(r), x, y))                   # ¬LHS∃ ⇔ ¬RHS∃
    eqR = equiv_neg(equivalence_symetrie(_collapse_dn_typique(b, y, existe(x, et(a, non(r))))))
    return equivalence_transitivite(equivalence_transitivite(eqL, mid), eqR)


__all__ = ["existe_typique", "pourtout_typique",
           "c39_existe_typique", "c39_pourtout_typique",
           "c40_existe_typique", "c40_pourtout_typique",
           "c42_existe_typique", "c42_pourtout_typique"]
