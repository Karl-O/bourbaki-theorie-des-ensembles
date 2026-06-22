"""§II.2 / §III.6 — Distribution ENSEMBLISTE PLEINE du produit cartésien sur la
réunion, à GAUCHE, et le corollaire `(A∪B)² = (A×A)∪((A×B)∪((B×A)∪(B×B)))`.

TASK A (Hessenberg a²=a, bottom-up).  On lève l'égalité ENSEMBLISTE
`(A∪B)×C = (A×C)∪(B×C)` (0 hyp) par EXTENSIONNALITÉ (A1) à partir du cœur
POINTWISE déjà clos `couple_dans_produit_reunion_gauche`
((u,v)∈(A∪B)×C ⇔ (u,v)∈(A×C)∪(B×C)), en POUSSANT le ∃p∃q de AXIOME_PRODUIT à
travers le ∨ via le helper `existe_ou` ((∃x)(P∨Q) ⇔ (∃x)P∨(∃x)Q, C33).

Puis le corollaire `carre_reunion_S0_U` ⊢ (S₀∪U)² = (S₀×S₀)∪F avec F la forme
EXACTE de `cadre_card_trois_b`, par double distribution (gauche puis droite) +
congruence de la réunion.

INVARIANT : theorie_ensembles()=22 ; aucun axiome ajouté ; rien postulé ; 0 hyp.
Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.logique.formule import (
    Terme, var, egal, et, ou, existe, appartient,
)
from bourbaki.logique import noyau_abrege as N
from bourbaki.ensembles import ensembles_abrege as E

from bourbaki.logique.tactiques.tactiques_abrege import syllogisme
from bourbaki.logique.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere,
    equivalence_transitivite, equivalence_symetrie, instancie, cas,
)
from bourbaki.logique.tactiques.tactiques_abrege_quantif import (
    monotonie_existe, existe_elimination, congruence_existe,
)
from bourbaki.ensembles.familles.ensembles_produit import _instance_produit
from bourbaki.ensembles.ensembles_theoremes import (
    _instance_reunion, egalite_par_extension,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


# ════════════════════════════════════════════════════════════════════════════
#  HELPER C33 — (∃x)(P ∨ Q) ⇔ ((∃x)P ∨ (∃x)Q).
# ════════════════════════════════════════════════════════════════════════════
def existe_ou(x, p, q):
    """⊢ (∃x)(P ∨ Q) ⇔ ((∃x)P ∨ (∃x)Q).   [CLOS, 0 hyp].   (C33, distribution ∃/∨.)"""
    exP, exQ = existe(x, p), existe(x, q)
    PorQ = ou(p, q)
    # ── ⇒ : (∃x)(P∨Q) ⇒ ((∃x)P ∨ (∃x)Q),  corps (P∨Q)⇒… par cas.
    hpq = N.assume(PorQ)
    brA = syllogisme(N.s5(p, var(x), x), N.s2(exP, exQ))        # P⇒(∃x)P⇒(∨)
    brB = syllogisme(N.s5(q, var(x), x),
                     syllogisme(N.s2(exQ, exP), N.s3(exQ, exP)))  # Q⇒(∃x)Q⇒(∨)
    corps = N.loi_deduction(PorQ, cas(hpq, brA, brB))
    fwd = existe_elimination(corps, x)
    # ── ⇐ : ((∃x)P ∨ (∃x)Q) ⇒ (∃x)(P∨Q), par cas.
    hdisj = N.assume(ou(exP, exQ))
    cA = monotonie_existe(N.s2(p, q), x)                       # (∃x)P⇒(∃x)(P∨Q)
    cB = monotonie_existe(syllogisme(N.s2(q, p), N.s3(q, p)), x)  # (∃x)Q⇒(∃x)(P∨Q)
    bwd = N.loi_deduction(ou(exP, exQ), cas(hdisj, cA, cB))
    return conjonction_intro(fwd, bwd)


# ════════════════════════════════════════════════════════════════════════════
#  corps : ( z=(p,q) et (p∈A∪B et q∈C) ) ⇔ ( bA ∨ bB ).
# ════════════════════════════════════════════════════════════════════════════
def _equiv_corps(a, b, c, z="z"):
    """⊢ ( z=(p,q) et (p∈A∪B et q∈C) ) ⇔
         ( ( z=(p,q) et (p∈A et q∈C) ) ∨ ( z=(p,q) et (p∈B et q∈C) ) ).

    p,q,z des variables fraîches (p,q liés ultérieurement). Preuve par déduction +
    cas sur p∈A∪B ⇔ (p∈A∨p∈B)."""
    vA, vB, vC, vz = _t(a), _t(b), _t(c), var(z)
    vp, vq = var("p"), var("q")
    eqz = egal(vz, E.couple(vp, vq))
    pAB, pA, pB, qC = (appartient(vp, E.reunion(vA, vB)), appartient(vp, vA),
                       appartient(vp, vB), appartient(vq, vC))
    bA = et(et(eqz, pA), qC)
    bB = et(et(eqz, pB), qC)
    lhs = et(et(eqz, pAB), qC)
    runion = _instance_reunion(vA, vB, vp)                      # pAB ⇔ (pA∨pB)

    # ── ⇒ : lhs ⇒ (bA∨bB) ────────────────────────────────────────────────────
    h = N.assume(lhs)
    left = conjonction_elim_gauche(h)                          # z=(p,q) et pAB
    z_eq = conjonction_elim_gauche(left)                       # z=(p,q)
    q_in = conjonction_elim_droite(h)                          # qC
    p_or = N.modus_ponens(conjonction_elim_droite(left), equivalence_avant(runion))  # pA∨pB
    # pA ⇒ bA ⇒ (bA∨bB)
    mkbA = N.loi_deduction(pA, conjonction_intro(conjonction_intro(z_eq, N.assume(pA)), q_in))
    brA = syllogisme(mkbA, N.s2(bA, bB))
    # pB ⇒ bB ⇒ (bA∨bB)
    mkbB = N.loi_deduction(pB, conjonction_intro(conjonction_intro(z_eq, N.assume(pB)), q_in))
    brB = syllogisme(mkbB, syllogisme(N.s2(bB, bA), N.s3(bB, bA)))
    rhs_from_lhs = cas(p_or, brA, brB)                         # bA∨bB  (sous {lhs})
    fwd = N.loi_deduction(lhs, rhs_from_lhs)

    # ── ⇐ : (bA∨bB) ⇒ lhs ────────────────────────────────────────────────────
    def rebuild(branch_p, pmem):
        hb = N.assume(branch_p)                                # (z=(p,q) et pX) et qC
        lft = conjonction_elim_gauche(hb)                      # z=(p,q) et pX
        ze = conjonction_elim_gauche(lft)
        pX = conjonction_elim_droite(lft)
        qc = conjonction_elim_droite(hb)
        pab = N.modus_ponens(N.modus_ponens(pX, pmem), equivalence_arriere(runion))  # pAB
        return N.loi_deduction(branch_p, conjonction_intro(conjonction_intro(ze, pab), qc))
    inA = rebuild(bA, N.s2(pA, pB))                            # pA⇒(pA∨pB)
    inB = rebuild(bB, syllogisme(N.s2(pB, pA), N.s3(pB, pA)))  # pB⇒(pA∨pB)
    hdisj = N.assume(ou(bA, bB))
    bwd = N.loi_deduction(ou(bA, bB), cas(hdisj, inA, inB))
    return conjonction_intro(fwd, bwd)


# ════════════════════════════════════════════════════════════════════════════
#  caractérisation (∀z) de (A∪B)×C  et  de (A×C)∪(B×C)  par la MÊME R.
# ════════════════════════════════════════════════════════════════════════════
def _R(a, b, c, z="z"):
    """R = (∃p)(∃q)bA ∨ (∃p)(∃q)bB  (le 'corps existentiel' partagé)."""
    vA, vB, vC, vz = _t(a), _t(b), _t(c), var(z)
    vp, vq = var("p"), var("q")
    eqz = egal(vz, E.couple(vp, vq))
    qC = appartient(vq, vC)
    bA = et(et(eqz, appartient(vp, vA)), qC)
    bB = et(et(eqz, appartient(vp, vB)), qC)
    exA = existe("p", existe("q", bA))
    exB = existe("p", existe("q", bB))
    return ou(exA, exB), bA, bB


def _char_gauche(a, b, c, z="z"):
    """⊢ (∀z)( z∈(A∪B)×C ⇔ R )."""
    vA, vB, vC = _t(a), _t(b), _t(c)
    R, bA, bB = _R(a, b, c, z)
    AB = E.reunion(vA, vB)
    e0 = _instance_produit(AB, vC, var(z))                     # z∈(A∪B)×C ⇔ (∃p∃q)body0
    e1 = congruence_existe(congruence_existe(_equiv_corps(a, b, c, z), "q"), "p")
    e2 = congruence_existe(existe_ou("q", bA, bB), "p")        # (∃p)(∃q)(bA∨bB)⇔(∃p)((∃q)bA∨(∃q)bB)
    e3 = existe_ou("p", existe("q", bA), existe("q", bB))      # ⇔ R
    chain = equivalence_transitivite(
        equivalence_transitivite(equivalence_transitivite(e0, e1), e2), e3)
    return N.generalisation(z, chain)


def _char_droite(a, b, c, z="z"):
    """⊢ (∀z)( z∈(A×C)∪(B×C) ⇔ R )."""
    vA, vB, vC, vz = _t(a), _t(b), _t(c), var(z)
    R, bA, bB = _R(a, b, c, z)
    AC, BC = E.produit(vA, vC), E.produit(vB, vC)
    # z∈(A×C)∪(B×C) ⇔ (z∈A×C ∨ z∈B×C)
    e0 = _instance_reunion(AC, BC, vz)
    # z∈A×C ⇔ (∃p∃q)bA  ;  z∈B×C ⇔ (∃p∃q)bB
    eA = _instance_produit(vA, vC, vz)
    eB = _instance_produit(vB, vC, vz)
    from bourbaki.logique.tactiques.tactiques_abrege2 import ou_congruence
    e1 = ou_congruence(eA, eB)                                 # (z∈A×C∨z∈B×C) ⇔ R
    chain = equivalence_transitivite(e0, e1)
    return N.generalisation(z, chain)


# ════════════════════════════════════════════════════════════════════════════
#  TASK A — égalité ENSEMBLISTE (A∪B)×C = (A×C)∪(B×C).
# ════════════════════════════════════════════════════════════════════════════
def produit_union_gauche(a="A", b="B", c="C", z="z"):
    """⊢ (A∪B)×C = (A×C)∪(B×C).   [CLOS, 0 hyp]   (E.II.2, distribution gauche)."""
    vA, vB, vC = _t(a), _t(b), _t(c)
    cg = _char_gauche(a, b, c, z)
    cd = _char_droite(a, b, c, z)
    tu = E.produit(E.reunion(vA, vB), vC)
    tv = E.reunion(E.produit(vA, vC), E.produit(vB, vC))
    res = egalite_par_extension(cg, cd, tu, tv, x=z)
    assert res.conclusion == egal(tu, tv), res.conclusion
    assert not res.hypotheses, "produit_union_gauche : NON clos !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  TASK A (droite) — A×(B∪C) = (A×B)∪(A×C)  (mirror).
# ════════════════════════════════════════════════════════════════════════════
def _equiv_corps_droite(a, b, c, z="z"):
    """⊢ ( z=(p,q) et (p∈A et q∈B∪C) ) ⇔ ( bB ∨ bC )  avec
         bB=(z=(p,q) et (p∈A et q∈B)), bC=(z=(p,q) et (p∈A et q∈C))."""
    vA, vB, vC, vz = _t(a), _t(b), _t(c), var(z)
    vp, vq = var("p"), var("q")
    eqz = egal(vz, E.couple(vp, vq))
    pA, qBC, qB, qC = (appartient(vp, vA), appartient(vq, E.reunion(vB, vC)),
                       appartient(vq, vB), appartient(vq, vC))
    bB = et(et(eqz, pA), qB)
    bC = et(et(eqz, pA), qC)
    lhs = et(et(eqz, pA), qBC)
    runion = _instance_reunion(vB, vC, vq)                      # qBC ⇔ (qB∨qC)
    # ⇒
    h = N.assume(lhs)
    left = conjonction_elim_gauche(h)                          # z=(p,q) et pA
    q_or = N.modus_ponens(conjonction_elim_droite(h), equivalence_avant(runion))  # qB∨qC
    mkbB = N.loi_deduction(qB, conjonction_intro(left, N.assume(qB)))
    brB = syllogisme(mkbB, N.s2(bB, bC))
    mkbC = N.loi_deduction(qC, conjonction_intro(left, N.assume(qC)))
    brC = syllogisme(mkbC, syllogisme(N.s2(bC, bB), N.s3(bC, bB)))
    fwd = N.loi_deduction(lhs, cas(q_or, brB, brC))
    # ⇐
    def rebuild(branch, qmem):
        hb = N.assume(branch)
        lft = conjonction_elim_gauche(hb)                      # z=(p,q) et pA
        qx = conjonction_elim_droite(hb)
        qbc = N.modus_ponens(N.modus_ponens(qx, qmem), equivalence_arriere(runion))  # qBC
        return N.loi_deduction(branch, conjonction_intro(lft, qbc))
    inB = rebuild(bB, N.s2(qB, qC))
    inC = rebuild(bC, syllogisme(N.s2(qC, qB), N.s3(qC, qB)))
    hdisj = N.assume(ou(bB, bC))
    bwd = N.loi_deduction(ou(bB, bC), cas(hdisj, inB, inC))
    return conjonction_intro(fwd, bwd)


def _R_droite(a, b, c, z="z"):
    vA, vB, vC, vz = _t(a), _t(b), _t(c), var(z)
    vp, vq = var("p"), var("q")
    eqz = egal(vz, E.couple(vp, vq))
    pA = appartient(vp, vA)
    bB = et(et(eqz, pA), appartient(vq, vB))
    bC = et(et(eqz, pA), appartient(vq, vC))
    return ou(existe("p", existe("q", bB)), existe("p", existe("q", bC))), bB, bC


def _char_gauche_droite(a, b, c, z="z"):
    """⊢ (∀z)( z∈A×(B∪C) ⇔ R_droite )."""
    vA, vB, vC = _t(a), _t(b), _t(c)
    R, bB, bC = _R_droite(a, b, c, z)
    BC = E.reunion(vB, vC)
    e0 = _instance_produit(vA, BC, var(z))
    e1 = congruence_existe(congruence_existe(_equiv_corps_droite(a, b, c, z), "q"), "p")
    e2 = congruence_existe(existe_ou("q", bB, bC), "p")
    e3 = existe_ou("p", existe("q", bB), existe("q", bC))
    chain = equivalence_transitivite(
        equivalence_transitivite(equivalence_transitivite(e0, e1), e2), e3)
    return N.generalisation(z, chain)


def _char_droite_droite(a, b, c, z="z"):
    """⊢ (∀z)( z∈(A×B)∪(A×C) ⇔ R_droite )."""
    from bourbaki.logique.tactiques.tactiques_abrege2 import ou_congruence
    vA, vB, vC, vz = _t(a), _t(b), _t(c), var(z)
    R, bB, bC = _R_droite(a, b, c, z)
    AB, AC = E.produit(vA, vB), E.produit(vA, vC)
    e0 = _instance_reunion(AB, AC, vz)
    eB = _instance_produit(vA, vB, vz)
    eC = _instance_produit(vA, vC, vz)
    e1 = ou_congruence(eB, eC)
    return N.generalisation(z, equivalence_transitivite(e0, e1))


def produit_union_droite(a="A", b="B", c="C", z="z"):
    """⊢ A×(B∪C) = (A×B)∪(A×C).   [CLOS, 0 hyp]   (E.II.2, distribution droite)."""
    vA, vB, vC = _t(a), _t(b), _t(c)
    cg = _char_gauche_droite(a, b, c, z)
    cd = _char_droite_droite(a, b, c, z)
    tu = E.produit(vA, E.reunion(vB, vC))
    tv = E.reunion(E.produit(vA, vB), E.produit(vA, vC))
    res = egalite_par_extension(cg, cd, tu, tv, x=z)
    assert res.conclusion == egal(tu, tv), res.conclusion
    assert not res.hypotheses, "produit_union_droite : NON clos !"
    return res


# ════════════════════════════════════════════════════════════════════════════
#  TASK A — (A∪B)² = (A×A)∪((A×B)∪((B×A)∪(B×B))).
# ════════════════════════════════════════════════════════════════════════════
def produit_union_carre(a="A", b="B", z="z"):
    """⊢ (A∪B)×(A∪B) = (A×A)∪((A×B)∪((B×A)∪(B×B))).   [CLOS, 0 hyp]."""
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import congruence_terme, composer_egalites
    from bourbaki.ensembles.ensembles_algebre_booleenne import associativite_reunion
    vA, vB = _t(a), _t(b)
    AB = E.reunion(vA, vB)
    AA, AxB, BxA, BB = (E.produit(vA, vA), E.produit(vA, vB),
                        E.produit(vB, vA), E.produit(vB, vB))
    # step1 : (A∪B)×(A∪B) = (A×(A∪B)) ∪ (B×(A∪B))     [gauche, C := A∪B]
    step1 = produit_union_gauche(a, b, AB, z)
    rhs1 = step1.conclusion.termes[1]                          # (A×(A∪B))∪(B×(A∪B))
    # step2a : A×(A∪B) = (A×A)∪(A×B)
    step2a = produit_union_droite(a, a, b, z)
    # step2b : B×(A∪B) = (B×A)∪(B×B)
    step2b = produit_union_droite(b, a, b, z)
    # réécrire rhs1 : remplacer le sous-terme gauche puis droit (congruence ∪)
    AxAB, BxAB = E.produit(vA, AB), E.produit(vB, AB)
    # rhs1 = AxAB ∪ BxAB.  remplacer AxAB par (A×A)∪(A×B) :
    cong_g = N.modus_ponens(step2a, congruence_terme(
        AxAB, E.reunion(AA, AxB), E.reunion(var("w"), BxAB)))   # rhs1 = ((A×A)∪(A×B))∪BxAB
    inter1 = composer_egalites(step1, cong_g)                  # (A∪B)² = ((A×A)∪(A×B))∪BxAB
    cong_d = N.modus_ponens(step2b, congruence_terme(
        BxAB, E.reunion(BxA, BB), E.reunion(E.reunion(AA, AxB), var("w"))))
    inter2 = composer_egalites(inter1, cong_d)                 # = ((A×A)∪(A×B))∪((B×A)∪(B×B))
    # associativité : ((A×A)∪(A×B))∪Z = (A×A)∪((A×B)∪Z),  Z=(B×A)∪(B×B)
    Z = E.reunion(BxA, BB)
    assoc = associativite_reunion(AA, AxB, Z)                  # ((A×A)∪(A×B))∪Z = (A×A)∪((A×B)∪Z)
    res = composer_egalites(inter2, assoc)
    cible = egal(E.produit(AB, AB), E.reunion(AA, E.reunion(AxB, Z)))
    assert res.conclusion == cible, f"{res.conclusion}\nvs\n{cible}"
    assert not res.hypotheses, "produit_union_carre : NON clos !"
    return res


def carre_reunion_S0_U(S="S0", U="Ucadre", z="z"):
    """⊢ (S₀∪U)×(S₀∪U) = (S₀×S₀)∪((S₀×U)∪((U×S₀)∪(U×U))).   [CLOS, 0 hyp].

    Corollaire de `produit_union_carre` aux noms S₀,U.  La forme RHS est la
    décomposition GÉOMÉTRIQUE (S₀×S₀)∪F (F = cadre, en RÉUNION) ; la version
    SOMME-DISJOINTE de `cadre_card_trois_b` s'en déduit sous disjointness (séparé)."""
    return produit_union_carre(S, U, z)


def s0sq_cadre_reunion_egale_carre(S="S0", U="Ucadre", z="z"):
    """⊢ (S₀×S₀) ∪ ((S₀×U)∪((U×S₀)∪(U×U)))  =  (S₀∪U)×(S₀∪U).   [CLOS, 0 hyp].

    🎯 TASK B — la SET-IDENTITY DOMAINE `S₀²∪F = Z²` dans sa forme RÉUNION-FRAME
    (F = (S₀×U)∪((U×S₀)∪(U×U)) en RÉUNION, NON somme-disjointe), 0 hyp, par
    symétrie de `carre_reunion_S0_U`.

    ⚠️ BLOCKER (honnête) : ce N'EST PAS la résiduelle hyp 2 effective de
    `phi1_bijection_derivee`, qui utilise `cadre_ensemble = (S₀×U)⊔((U×S₀)⊔(U×U))`
    en SOMME-DISJOINTE (tags ×{0}/×{1}, `ensembles_somme_disjointe`).  Comme
    somme_disjointe(A,B)=(A×{0})∪(B×{1}) ≠ reunion(A,B), la résiduelle effective
    `(S₀×S₀)∪cadre⊔ = Z²` est un TERME DISTINCT, non égal à Z² (Z² a des éléments
    NON tagués).  Décharger hyp 2 demande de RE-CÂBLER ψ pour qu'elle ait pour
    domaine la frame en RÉUNION (pas en ⊔) — changement d'architecture de
    `phi_etendue_bijection`/`cadre_ensemble`, hors scope mécanique de TASK B."""
    from bourbaki.logique.tactiques.tactiques_abrege_egalite import symetrie
    cr = carre_reunion_S0_U(S, U, z)
    lhs, rhs = cr.conclusion.termes                         # Z² = S₀²∪F
    res = N.modus_ponens(cr, symetrie(lhs, rhs))            # S₀²∪F = Z²
    assert res.conclusion == egal(rhs, lhs)
    assert not res.hypotheses, "s0sq_cadre_reunion_egale_carre : NON clos !"
    return res


__all__ = [
    "existe_ou",
    "produit_union_gauche",
    "produit_union_droite",
    "produit_union_carre",
    "carre_reunion_S0_U",
    "s0sq_cadre_reunion_egale_carre",
]
