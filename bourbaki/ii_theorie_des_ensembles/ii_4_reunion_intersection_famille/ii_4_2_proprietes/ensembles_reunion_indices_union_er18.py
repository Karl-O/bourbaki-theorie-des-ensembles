"""Résumé §4 (E.R.18 item 3, formule (36)) — réunion sur J₁∪J₂ = réunion des deux.

Bourbaki (E.R.18, formule (36)) :  ⋃_{ι∈J₁∪J₂} X_ι = (⋃_{ι∈J₁} X_ι) ∪ (⋃_{ι∈J₂} X_ι).

ÉNONCÉ DÉRIVÉ (f = famille (X_ι)) :

    ⊢ reunion_famille(f, J₁∪J₂) = reunion( reunion_famille(f,J₁), reunion_famille(f,J₂) ).

DÉMONSTRATION — extensionnalité + chaîne d'équivalences d'appartenance :
  z∈⋃_{J₁∪J₂}X_ι
   ⇔ (∃i)( i∈J₁∪J₂ et z∈X_i )                 [membre_reunion_famille, I:=J₁∪J₂]
   ⇔ (∃i)( (i∈J₁ ou i∈J₂) et z∈X_i )           [_instance_reunion binaire, sous congruence_existe]
   ⇔ (∃i)( (i∈J₁ et z∈X_i) ou (i∈J₂ et z∈X_i) ) [commute_et + et_ou_distrib, sous congruence_existe]
   ⇔ (∃i)(i∈J₁ et z∈X_i) ou (∃i)(i∈J₂ et z∈X_i) [distribution ∃ sur ∨ — helper local]
   ⇔ z∈⋃_{J₁}X_ι ou z∈⋃_{J₂}X_ι                 [membre_reunion_famille]
   ⇔ z∈(⋃_{J₁})∪(⋃_{J₂}).                        [_instance_reunion binaire]

theorie_ensembles() inchangée (22 axiomes).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    var, et, ou, egal, appartient, existe, inclus, Terme)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
    et_ou_distrib, ou_congruence, et_congruence_gauche, equivalence_transitivite)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, congruence_existe, monotonie_existe)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    _instance_reunion, extensionnalite_appliquee)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_1_definitions_algebre.ensembles_familles import (
    membre_reunion_famille)


def _t(v):
    return v if isinstance(v, Terme) else var(v)


def _equiv_sym(thm):
    """⊢ (A⇔B)  ⟹  ⊢ (B⇔A)   (equiv = et(A⇒B, B⇒A))."""
    return conjonction_intro(conjonction_elim_droite(thm), conjonction_elim_gauche(thm))


def _commute_et(p, q):
    """⊢ (P et Q) ⇔ (Q et P)."""
    h1 = N.assume(et(p, q))
    f1 = N.loi_deduction(et(p, q), conjonction_intro(conjonction_elim_droite(h1),
                                                     conjonction_elim_gauche(h1)))
    h2 = N.assume(et(q, p))
    f2 = N.loi_deduction(et(q, p), conjonction_intro(conjonction_elim_droite(h2),
                                                     conjonction_elim_gauche(h2)))
    return conjonction_intro(f1, f2)


def _existe_ou(x, P, Q):
    """⊢ (∃x)(P ou Q) ⇔ ( (∃x)P ou (∃x)Q ).   (P, Q : formules à x éventuellement libre.)"""
    vx = var(x)
    exP, exQ = existe(x, P), existe(x, Q)
    RHS = ou(exP, exQ)
    # ── fwd : (∃x)(P∨Q) ⇒ RHS ─────────────────────────────────────────────────
    caseP = N.loi_deduction(P, N.modus_ponens(N.modus_ponens(N.assume(P), N.s5(P, vx, x)),
                                              N.s2(exP, exQ)))                     # P ⇒ RHS
    q_or = N.modus_ponens(N.modus_ponens(N.modus_ponens(N.assume(Q), N.s5(Q, vx, x)),
                                         N.s2(exQ, exP)), N.s3(exQ, exP))          # RHS  [sous Q]
    caseQ = N.loi_deduction(Q, q_or)                                              # Q ⇒ RHS
    inner = cas(N.assume(ou(P, Q)), caseP, caseQ)                                 # {P∨Q} ⊢ RHS
    fwd = existe_elimination(N.loi_deduction(ou(P, Q), inner), x)                 # (∃x)(P∨Q) ⇒ RHS
    # ── bwd : RHS ⇒ (∃x)(P∨Q) ─────────────────────────────────────────────────
    exP_imp = monotonie_existe(N.s2(P, Q), x)                                     # (∃x)P ⇒ (∃x)(P∨Q)
    q_pq = N.loi_deduction(Q, N.modus_ponens(N.modus_ponens(N.assume(Q), N.s2(Q, P)), N.s3(Q, P)))  # Q⇒(P∨Q)
    exQ_imp = monotonie_existe(q_pq, x)                                           # (∃x)Q ⇒ (∃x)(P∨Q)
    caseeP = N.loi_deduction(exP, N.modus_ponens(N.assume(exP), exP_imp))
    caseeQ = N.loi_deduction(exQ, N.modus_ponens(N.assume(exQ), exQ_imp))
    bwd = N.loi_deduction(RHS, cas(N.assume(RHS), caseeP, caseeQ))                # RHS ⇒ (∃x)(P∨Q)
    return conjonction_intro(fwd, bwd)


def enonce_reunion_indices_union(f="f", j1="J1", j2="J2"):
    vf, vJ1, vJ2 = _t(f), _t(j1), _t(j2)
    U12 = E.reunion_famille(vf, E.reunion(vJ1, vJ2))
    U1 = E.reunion_famille(vf, vJ1)
    U2 = E.reunion_famille(vf, vJ2)
    return egal(U12, E.reunion(U1, U2))


# @livre Ch.R §4 Prop.- | E.R.18 item 3 formule (36) | PDF p.321  (⋃_{J₁∪J₂}=⋃_{J₁}∪⋃_{J₂} — DÉRIVÉ)
# @livre Ch.R §4 Demo.- | E.R.18 item 3 | PDF p.321  (démo : chaîne d'appartenance + distribution ∃/∨ + extensionnalité)
def reunion_indices_union(f="f", j1="J1", j2="J2"):
    """🎯 ⊢ ⋃_{ι∈J₁∪J₂} X_ι = (⋃_{ι∈J₁} X_ι) ∪ (⋃_{ι∈J₂} X_ι)   (E.R.18 (36))."""
    vf, vJ1, vJ2 = _t(f), _t(j1), _t(j2)
    vz, vi = var("z"), var("i")
    Xi = E.valeur_famille(vf, vi)                       # X_i
    U12 = E.reunion_famille(vf, E.reunion(vJ1, vJ2))
    U1 = E.reunion_famille(vf, vJ1)
    U2 = E.reunion_famille(vf, vJ2)

    z_in_Xi = appartient(vz, Xi)
    i_in_J1, i_in_J2 = appartient(vi, vJ1), appartient(vi, vJ2)
    bodyA = et(i_in_J1, z_in_Xi)                        # i∈J₁ et z∈X_i
    bodyB = et(i_in_J2, z_in_Xi)                        # i∈J₂ et z∈X_i

    # A : z∈U12 ⇔ (∃i)( i∈(J₁∪J₂) et z∈X_i )
    A = instancie(N.generalisation("I", membre_reunion_famille("f", "I", "z")), E.reunion(vJ1, vJ2))

    # B : corps  i∈(J₁∪J₂) et z∈X_i  ⇔  (i∈J₁ ou i∈J₂) et z∈X_i
    eqmem = _instance_reunion(vJ1, vJ2, vi)             # (i∈J₁∪J₂) ⇔ (i∈J₁ ou i∈J₂)
    congB = congruence_existe(et_congruence_gauche(eqmem, z_in_Xi), "i")

    # C : (i∈J₁ ou i∈J₂) et z∈X_i  ⇔  (i∈J₁ et z∈X_i) ou (i∈J₂ et z∈X_i)
    e1 = _commute_et(ou(i_in_J1, i_in_J2), z_in_Xi)     # ((..∨..)∧p) ⇔ (p∧(..∨..))
    e2 = et_ou_distrib(z_in_Xi, i_in_J1, i_in_J2)       # (p∧(Q∨R)) ⇔ ((p∧Q)∨(p∧R))
    e3 = ou_congruence(_commute_et(z_in_Xi, i_in_J1), _commute_et(z_in_Xi, i_in_J2))
    body2_body3 = equivalence_transitivite(equivalence_transitivite(e1, e2), e3)
    congC = congruence_existe(body2_body3, "i")

    # D : (∃i)(bodyA ou bodyB) ⇔ (∃i)bodyA ou (∃i)bodyB
    D = _existe_ou("i", bodyA, bodyB)

    # E : (∃i)bodyA ⇔ z∈U1  et  (∃i)bodyB ⇔ z∈U2   (membre_reunion_famille, symétrisé)
    E_eq = ou_congruence(_equiv_sym(membre_reunion_famille("f", "J1", "z")),
                         _equiv_sym(membre_reunion_famille("f", "J2", "z")))

    # F : (z∈U1 ou z∈U2) ⇔ z∈(U1∪U2)
    F = _equiv_sym(_instance_reunion(U1, U2, vz))

    EQ = equivalence_transitivite(
        equivalence_transitivite(
            equivalence_transitivite(
                equivalence_transitivite(
                    equivalence_transitivite(A, congB), congC), D), E_eq), F)   # z∈U12 ⇔ z∈(U1∪U2)

    incl1 = N.generalisation("z", N.loi_deduction(
        appartient(vz, U12), N.modus_ponens(N.assume(appartient(vz, U12)), equivalence_avant(EQ))))
    incl2 = N.generalisation("z", N.loi_deduction(
        appartient(vz, E.reunion(U1, U2)),
        N.modus_ponens(N.assume(appartient(vz, E.reunion(U1, U2))), equivalence_arriere(EQ))))
    res = N.modus_ponens(conjonction_intro(incl1, incl2), extensionnalite_appliquee(U12, E.reunion(U1, U2)))
    assert res.conclusion == enonce_reunion_indices_union(f, j1, j2), \
        "reunion_indices_union : conclusion ≠ énoncé attendu"
    return res


__all__ = ["enonce_reunion_indices_union", "reunion_indices_union"]
