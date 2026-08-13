"""§II.1 — ALGÈBRE de la réunion / l'intersection : associativité, idempotence,
absorption (égalités ensemblistes, lois de treillis booléen).

Bourbaki E.II.1 (et formulaire) : ∪ et ∩ sont associatives, idempotentes, et liées
par les lois d'absorption.  La commutativité est déjà certifiée
(`ensembles_theoremes.commutativite_reunion/intersection`).  On complète ici :

    (A∪B)∪C = A∪(B∪C)        (A∩B)∩C = A∩(B∩C)        A∪A = A    A∩A = A
    A∪(A∩B) = A              A∩(A∪B) = A

Toutes CLOSES (0 hyp), par extensionnalité (`egalite_par_extension`) à partir des
axiomes de membership ∪/∩ (AXIOME_REUNION/INTER, dans les 22) et de lois
propositionnelles fermées (associativité/idempotence/absorption de ∨ et ∧, prouvées
ici au niveau du noyau).  theorie_ensembles() INCHANGÉE = 22 ; aucun axiome ajouté.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import Terme, var, appartient, et, ou, non
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import _instance_reunion, egalite_par_extension
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege import a_implique_a
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    et_congruence_droite, et_congruence_gauche, ou_congruence,
    equivalence_transitivite, equivalence_symetrie, assoc_et, et_ou_distrib,
    cas, syllogisme, demorgan_ou, demorgan_et, equiv_neg,
)


def _t(x):
    return x if isinstance(x, Terme) else var(x)


def _instance_inter(a, b, z):
    """⊢ (z ∈ a∩b) ⇔ (z∈a et z∈b)   (instance de AXIOME_INTER aux termes a,b,z)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_INTER)
    return instancie(instancie(instancie(ax, a), b), z)


def _instance_diff(e, x, z):
    """⊢ (z ∈ e∖x) ⇔ (z∈e et ¬(z∈x))   (instance de AXIOME_DIFF aux termes e,x,z)."""
    from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import instancie
    ax = N.axiome(E.theorie_ensembles(), E.AXIOME_DIFF)
    return instancie(instancie(instancie(ax, e), x), z)


def _et_et_distrib(p, q, r):
    """⊢ (P et (Q et R)) ⇔ ((P et Q) et (P et R))   (P dupliqué)."""
    hf = N.assume(et(p, et(q, r)))
    pp, qr = conjonction_elim_gauche(hf), conjonction_elim_droite(hf)
    fwd = N.loi_deduction(et(p, et(q, r)), conjonction_intro(
        conjonction_intro(pp, conjonction_elim_gauche(qr)),
        conjonction_intro(pp, conjonction_elim_droite(qr))))
    hb = N.assume(et(et(p, q), et(p, r)))
    pq, pr = conjonction_elim_gauche(hb), conjonction_elim_droite(hb)
    bwd = N.loi_deduction(et(et(p, q), et(p, r)), conjonction_intro(
        conjonction_elim_gauche(pq),
        conjonction_intro(conjonction_elim_droite(pq), conjonction_elim_droite(pr))))
    return conjonction_intro(fwd, bwd)


def _refl_equiv(f):
    """⊢ (F ⇔ F)."""
    return conjonction_intro(a_implique_a(f), a_implique_a(f))


# ── ou-introductions (gauche / droite) ───────────────────────────────────────
def _oui_g(a, b):
    """⊢ A ⇒ (A∨B)."""
    return N.s2(a, b)


def _oui_d(a, b):
    """⊢ B ⇒ (A∨B)."""
    return syllogisme(N.s2(b, a), N.s3(b, a))   # B⇒(B∨A)⇒(A∨B)


# ── lois propositionnelles fermées ───────────────────────────────────────────
def _ou_idempotent(p):
    """⊢ (P∨P) ⇔ P."""
    inner = cas(N.assume(ou(p, p)), a_implique_a(p), a_implique_a(p))   # P sous (P∨P)
    fwd = N.loi_deduction(ou(p, p), inner)
    return conjonction_intro(fwd, _oui_g(p, p))


def _et_idempotent(p):
    """⊢ (P et P) ⇔ P."""
    fwd = N.loi_deduction(et(p, p), conjonction_elim_gauche(N.assume(et(p, p))))
    hp = N.assume(p)
    bwd = N.loi_deduction(p, conjonction_intro(hp, hp))
    return conjonction_intro(fwd, bwd)


def _assoc_ou(p, q, r):
    """⊢ ((P∨Q)∨R) ⇔ (P∨(Q∨R))."""
    QR, PQ = ou(q, r), ou(p, q)
    PQR_l, P_QR = ou(PQ, r), ou(p, QR)
    # ── fwd : (P∨Q)∨R ⇒ P∨(Q∨R) ──
    fromP = _oui_g(p, QR)                                  # P ⇒ P∨(Q∨R)
    fromQ = syllogisme(_oui_g(q, r), _oui_d(p, QR))        # Q ⇒ (Q∨R) ⇒ P∨(Q∨R)
    imp_PQ = N.loi_deduction(PQ, cas(N.assume(PQ), fromP, fromQ))   # (P∨Q) ⇒ P∨(Q∨R)
    fromR = syllogisme(_oui_d(q, r), _oui_d(p, QR))        # R ⇒ (Q∨R) ⇒ P∨(Q∨R)
    fwd = N.loi_deduction(PQR_l, cas(N.assume(PQR_l), imp_PQ, fromR))
    # ── bwd : P∨(Q∨R) ⇒ (P∨Q)∨R ──
    fromPb = syllogisme(_oui_g(p, q), _oui_g(PQ, r))       # P ⇒ (P∨Q) ⇒ (P∨Q)∨R
    fromQb = syllogisme(_oui_d(p, q), _oui_g(PQ, r))       # Q ⇒ (P∨Q) ⇒ (P∨Q)∨R
    fromRb = _oui_d(PQ, r)                                 # R ⇒ (P∨Q)∨R
    imp_QR = N.loi_deduction(QR, cas(N.assume(QR), fromQb, fromRb))  # (Q∨R) ⇒ (P∨Q)∨R
    bwd = N.loi_deduction(P_QR, cas(N.assume(P_QR), fromPb, imp_QR))
    return conjonction_intro(fwd, bwd)


def _absorption_ou(p, q):
    """⊢ (P∨(P et Q)) ⇔ P."""
    pq_to_p = N.loi_deduction(et(p, q), conjonction_elim_gauche(N.assume(et(p, q))))
    fwd = N.loi_deduction(ou(p, et(p, q)), cas(N.assume(ou(p, et(p, q))), a_implique_a(p), pq_to_p))
    return conjonction_intro(fwd, _oui_g(p, et(p, q)))


def _absorption_et(p, q):
    """⊢ (P et (P∨Q)) ⇔ P."""
    fwd = N.loi_deduction(et(p, ou(p, q)), conjonction_elim_gauche(N.assume(et(p, ou(p, q)))))
    hp = N.assume(p)
    bwd = N.loi_deduction(p, conjonction_intro(hp, N.modus_ponens(hp, _oui_g(p, q))))
    return conjonction_intro(fwd, bwd)


# ════════════════════════════════════════════════════════════════════════════
#  ÉGALITÉS ENSEMBLISTES  (E.II.1)
# ════════════════════════════════════════════════════════════════════════════
# @livre Ch.R §1.13 Rem.- | E.R.4 L.7-8 | PDF p.307
def associativite_reunion(a="A", b="B", c="C"):
    """⊢ (A∪B)∪C = A∪(B∪C)."""
    va, vb, vc, vz = _t(a), _t(b), _t(c), var("z")
    AB, BC = E.reunion(va, vb), E.reunion(vb, vc)
    zA, zB, zC = appartient(vz, va), appartient(vz, vb), appartient(vz, vc)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_reunion(AB, vc, vz),
        ou_congruence(_instance_reunion(va, vb, vz), _refl_equiv(zC))),
        _assoc_ou(zA, zB, zC)))
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_reunion(va, BC, vz),
        ou_congruence(_refl_equiv(zA), _instance_reunion(vb, vc, vz))))
    return egalite_par_extension(char_u, char_v, E.reunion(AB, vc), E.reunion(va, BC))


# @livre Ch.R §1.13 Rem.- | E.R.4 L.7-8 | PDF p.307
def associativite_intersection(a="A", b="B", c="C"):
    """⊢ (A∩B)∩C = A∩(B∩C)."""
    va, vb, vc, vz = _t(a), _t(b), _t(c), var("z")
    AB, BC = E.intersection(va, vb), E.intersection(vb, vc)
    zA, zB, zC = appartient(vz, va), appartient(vz, vb), appartient(vz, vc)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(AB, vc, vz),
        et_congruence_gauche(_instance_inter(va, vb, vz), zC)),
        equivalence_symetrie(assoc_et(zA, zB, zC))))
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_inter(va, BC, vz),
        et_congruence_droite(zA, _instance_inter(vb, vc, vz))))
    return egalite_par_extension(char_u, char_v, E.intersection(AB, vc), E.intersection(va, BC))


# @livre Ch.R §1.14 Prop.(2) | E.R.4 L.20-20 | PDF p.307
def idempotence_reunion(a="A"):
    """⊢ A∪A = A."""
    va, vz = _t(a), var("z")
    zA = appartient(vz, va)
    char_u = N.generalisation("z", equivalence_transitivite(_instance_reunion(va, va, vz),
                                                            _ou_idempotent(zA)))
    char_v = N.generalisation("z", _refl_equiv(zA))
    return egalite_par_extension(char_u, char_v, E.reunion(va, va), va)


# @livre Ch.R §1.14 Prop.(2) | E.R.4 L.20-20 | PDF p.307
def idempotence_intersection(a="A"):
    """⊢ A∩A = A."""
    va, vz = _t(a), var("z")
    zA = appartient(vz, va)
    char_u = N.generalisation("z", equivalence_transitivite(_instance_inter(va, va, vz),
                                                            _et_idempotent(zA)))
    char_v = N.generalisation("z", _refl_equiv(zA))
    return egalite_par_extension(char_u, char_v, E.intersection(va, va), va)


# @livre Ch.R §1.13 Rem.- | E.R.4 L.7-8 | PDF p.307
def absorption_reunion(a="A", b="B"):
    """⊢ A∪(A∩B) = A."""
    va, vb, vz = _t(a), _t(b), var("z")
    AB = E.intersection(va, vb)
    zA, zB = appartient(vz, va), appartient(vz, vb)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_reunion(va, AB, vz),
        ou_congruence(_refl_equiv(zA), _instance_inter(va, vb, vz))),
        _absorption_ou(zA, zB)))
    char_v = N.generalisation("z", _refl_equiv(zA))
    return egalite_par_extension(char_u, char_v, E.reunion(va, AB), va)


# @livre Ch.R §1.13 Rem.- | E.R.4 L.7-8 | PDF p.307
def absorption_intersection(a="A", b="B"):
    """⊢ A∩(A∪B) = A."""
    va, vb, vz = _t(a), _t(b), var("z")
    AB = E.reunion(va, vb)
    zA, zB = appartient(vz, va), appartient(vz, vb)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(va, AB, vz),
        et_congruence_droite(zA, _instance_reunion(va, vb, vz))),
        _absorption_et(zA, zB)))
    char_v = N.generalisation("z", _refl_equiv(zA))
    return egalite_par_extension(char_u, char_v, E.intersection(va, AB), va)


def _ou_et_distrib(p, q, r):
    """⊢ (P ou (Q et R)) ⇔ ((P ou Q) et (P ou R))   (distribution de ∨ sur et, dual)."""
    PQ, PR, QR = ou(p, q), ou(p, r), et(q, r)
    target = et(PQ, PR)
    # ── fwd : P∨(Q et R) ⇒ (P∨Q) et (P∨R) ──
    hp = N.assume(p)
    fromP = N.loi_deduction(p, conjonction_intro(N.modus_ponens(hp, _oui_g(p, q)),
                                                 N.modus_ponens(hp, _oui_g(p, r))))
    hqr = N.assume(QR)
    fromQR = N.loi_deduction(QR, conjonction_intro(
        N.modus_ponens(conjonction_elim_gauche(hqr), _oui_d(p, q)),
        N.modus_ponens(conjonction_elim_droite(hqr), _oui_d(p, r))))
    fwd = N.loi_deduction(ou(p, QR), cas(N.assume(ou(p, QR)), fromP, fromQR))
    # ── bwd : (P∨Q) et (P∨R) ⇒ P∨(Q et R) ──
    h = N.assume(target)
    hpq, hpr = conjonction_elim_gauche(h), conjonction_elim_droite(h)   # P∨Q ; P∨R
    p_to_goal = _oui_g(p, QR)                                           # P ⇒ P∨(Q et R)
    hq = N.assume(q)
    r_to_goal_uq = N.loi_deduction(r, N.modus_ponens(conjonction_intro(hq, N.assume(r)),
                                                     _oui_d(p, QR)))    # R ⇒ goal  (sous q)
    q_to_goal = N.loi_deduction(q, cas(hpr, p_to_goal, r_to_goal_uq))   # Q ⇒ goal
    bwd = N.loi_deduction(target, cas(hpq, p_to_goal, q_to_goal))
    return conjonction_intro(fwd, bwd)


# @livre Ch.R §1.13 Rem.- | E.R.4 L.7-8 | PDF p.307
def distributivite_intersection_reunion(a="A", b="B", c="C"):
    """⊢ A∩(B∪C) = (A∩B)∪(A∩C)   (distributivité de ∩ sur ∪, E.II.1)."""
    va, vb, vc, vz = _t(a), _t(b), _t(c), var("z")
    zA, zB, zC = appartient(vz, va), appartient(vz, vb), appartient(vz, vc)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(va, E.reunion(vb, vc), vz),
        et_congruence_droite(zA, _instance_reunion(vb, vc, vz))),
        et_ou_distrib(zA, zB, zC)))
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_reunion(E.intersection(va, vb), E.intersection(va, vc), vz),
        ou_congruence(_instance_inter(va, vb, vz), _instance_inter(va, vc, vz))))
    return egalite_par_extension(char_u, char_v, E.intersection(va, E.reunion(vb, vc)),
                                 E.reunion(E.intersection(va, vb), E.intersection(va, vc)))


# @livre Ch.R §1.13 Rem.- | E.R.4 L.7-8 | PDF p.307
def distributivite_reunion_intersection(a="A", b="B", c="C"):
    """⊢ A∪(B∩C) = (A∪B)∩(A∪C)   (distributivité de ∪ sur ∩, E.II.1)."""
    va, vb, vc, vz = _t(a), _t(b), _t(c), var("z")
    zA, zB, zC = appartient(vz, va), appartient(vz, vb), appartient(vz, vc)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_reunion(va, E.intersection(vb, vc), vz),
        ou_congruence(_refl_equiv(zA), _instance_inter(vb, vc, vz))),
        _ou_et_distrib(zA, zB, zC)))
    char_v = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(E.reunion(va, vb), E.reunion(va, vc), vz),
        et_congruence_gauche(_instance_reunion(va, vb, vz), appartient(vz, E.reunion(va, vc)))),
        et_congruence_droite(ou(zA, zB), _instance_reunion(va, vc, vz))))
    return egalite_par_extension(char_u, char_v, E.reunion(va, E.intersection(vb, vc)),
                                 E.intersection(E.reunion(va, vb), E.reunion(va, vc)))


# @livre Ch.R §1.14 Prop.(8) | E.R.4 L.27-27 | PDF p.307
def de_morgan_complement_reunion(e="E", a="A", b="B"):
    """⊢ E∖(A∪B) = (E∖A)∩(E∖B)   (De Morgan, complément relatif, E.II.1)."""
    vE, va, vb, vz = _t(e), _t(a), _t(b), var("z")
    zE, nA, nB = appartient(vz, vE), non(appartient(vz, va)), non(appartient(vz, vb))
    zA, zB = appartient(vz, va), appartient(vz, vb)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        _instance_diff(vE, E.reunion(va, vb), vz),
        et_congruence_droite(zE, equiv_neg(_instance_reunion(va, vb, vz)))),
        et_congruence_droite(zE, demorgan_ou(zA, zB))),
        _et_et_distrib(zE, nA, nB)))
    DEA, DEB = E.difference(vE, va), E.difference(vE, vb)
    char_v = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(
        _instance_inter(DEA, DEB, vz),
        et_congruence_gauche(_instance_diff(vE, va, vz), appartient(vz, DEB))),
        et_congruence_droite(et(zE, nA), _instance_diff(vE, vb, vz))))
    return egalite_par_extension(char_u, char_v, E.difference(vE, E.reunion(va, vb)),
                                 E.intersection(DEA, DEB))


# @livre Ch.R §1.14 Prop.(8) | E.R.4 L.27-27 | PDF p.307
def de_morgan_complement_intersection(e="E", a="A", b="B"):
    """⊢ E∖(A∩B) = (E∖A)∪(E∖B)   (De Morgan, complément relatif, E.II.1)."""
    vE, va, vb, vz = _t(e), _t(a), _t(b), var("z")
    zE, nA, nB = appartient(vz, vE), non(appartient(vz, va)), non(appartient(vz, vb))
    zA, zB = appartient(vz, va), appartient(vz, vb)
    char_u = N.generalisation("z", equivalence_transitivite(equivalence_transitivite(equivalence_transitivite(
        _instance_diff(vE, E.intersection(va, vb), vz),
        et_congruence_droite(zE, equiv_neg(_instance_inter(va, vb, vz)))),
        et_congruence_droite(zE, demorgan_et(zA, zB))),
        et_ou_distrib(zE, nA, nB)))
    DEA, DEB = E.difference(vE, va), E.difference(vE, vb)
    char_v = N.generalisation("z", equivalence_transitivite(
        _instance_reunion(DEA, DEB, vz),
        ou_congruence(_instance_diff(vE, va, vz), _instance_diff(vE, vb, vz))))
    return egalite_par_extension(char_u, char_v, E.difference(vE, E.intersection(va, vb)),
                                 E.reunion(DEA, DEB))


__all__ = [
    "associativite_reunion", "associativite_intersection",
    "idempotence_reunion", "idempotence_intersection",
    "absorption_reunion", "absorption_intersection",
    "distributivite_intersection_reunion", "distributivite_reunion_intersection",
    "de_morgan_complement_reunion", "de_morgan_complement_intersection",
]
