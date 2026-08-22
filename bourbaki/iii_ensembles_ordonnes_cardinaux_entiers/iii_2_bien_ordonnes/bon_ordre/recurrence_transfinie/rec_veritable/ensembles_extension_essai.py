# -*- coding: utf-8 -*-
"""§III.2.2 — R3', brique 1 : LA RESTRICTION EFFACE LE NOUVEAU POINT.

🎯 CIBLE (une hypothèse honnête) :

    restriction_reunion_singleton_hors :
        { ¬(x∈X) }  ⊢  (p ∪ {(x,v)}) | X  =  p | X

C'est la brique-clé de l'extension d'essai R3' (p' := p ∪ {(x, vh(p))}) :
l'équation de récursion de p' en un point z < x lit p'|seg(z) — qui doit être
p|seg(z) (le nouveau couple (x,·) est INVISIBLE sous x, car x ∉ seg(z)).
Au point x lui-même : p'|seg(x) = p|seg(x) = p (dom p = seg(x)), et la valeur
v := vh(p) vérifie l'équation par congruence.

PREUVE (double inclusion, AXIOME_RESTRICTION des deux côtés) :
  ⊆  z∈(p∪S)|X donne des témoins (pb,qb) : z=(pb,qb), pb∈X, (pb,qb)∈p∪S.
     • (pb,qb)∈p : on reconstruit les trois conjoints → z∈p|X ;
     • (pb,qb)∈S : (pb,qb)=(x,v) (singleton), pb=x (injectivité du couple),
       donc x∈X (Leibniz) — contredit ¬(x∈X) ; ex falso via l'encodage-∨.
  ⊇  z∈p|X : (pb,qb)∈p ⊂ p∪S (S2 + axiome-réunion), on reconstruit.
Les témoins portent les LIANTS DE L'AXIOME (« p », « q ») — les paramètres du
lemme (pes, xse, vse, Xse) sont nommés pour éviter toute capture.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, non, appartient, existe, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_pour_tout,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    singleton_membre, couple_egal_implique_composantes,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_briques import (
    _inst_restriction,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.recollement.ensembles_restriction_somme import (
    membre_reunion_graphes,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _corps_restriction(vz, F, vX):
    """Le corps-témoin de AXIOME_RESTRICTION (liants « p », « q » de l'axiome) :
    z=(p,q) ∧ p∈X ∧ (p,q)∈F."""
    vpb, vqb = var("p"), var("q")
    return et(et(egal(vz, E.couple(vpb, vqb)), appartient(vpb, vX)),
              appartient(E.couple(vpb, vqb), F))


def _reconstruire(vz, F, vX, z_eq, pb_X, pq_F):
    """Des trois conjoints prouvés, reconstruire z∈F|X (S5 ×2 sur les liants p,q)."""
    corps = _corps_restriction(vz, F, vX)
    corps_prouve = conjonction_intro(conjonction_intro(z_eq, pb_X), pq_F)
    ex_q = N.modus_ponens(corps_prouve, N.s5(corps, var("q"), "q"))
    ex_pq = N.modus_ponens(ex_q, N.s5(existe("q", corps), var("p"), "p"))
    return N.modus_ponens(ex_pq, equivalence_arriere(_inst_restriction(F, vX, vz)))


def restriction_reunion_singleton_hors(p="pes", x="xse", v="vse", X="Xse"):
    """{ ¬(x∈X) } ⊢ (p ∪ {(x,v)}) | X = p | X          [1 hyp honnête].

    Brique 1 de R3' — voir la docstring de module pour la preuve."""
    vp, vx, vv, vX = _t(p), _t(x), _t(v), _t(X)
    cxv = E.couple(vx, vv)
    S = E.singleton(cxv)
    pS = E.reunion(vp, S)
    rG = E.restriction(pS, vX)                              # (p∪S)|X
    rD = E.restriction(vp, vX)                              # p|X
    vz = var("zre")
    vpb, vqb = var("p"), var("q")
    cpl = E.couple(vpb, vqb)

    h_notx = N.assume(non(appartient(vx, vX)))              # ¬(x∈X)     [HONNÊTE]

    # ── (⊆) z∈(p∪S)|X ⇒ z∈p|X ────────────────────────────────────────────────
    h_z1 = N.assume(appartient(vz, rG))
    ex1 = N.modus_ponens(h_z1, equivalence_avant(_inst_restriction(pS, vX, vz)))
    corps_G = _corps_restriction(vz, pS, vX)
    h_b = N.assume(corps_G)                                 # témoins p, q
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(h_b))   # z=(p,q)
    pb_X = conjonction_elim_droite(conjonction_elim_gauche(h_b))   # p∈X
    pq_pS = conjonction_elim_droite(h_b)                           # (p,q)∈p∪S
    disj = N.modus_ponens(pq_pS, equivalence_avant(
        membre_reunion_graphes(vp, S, cpl)))                # (p,q)∈p ∨ (p,q)∈S
    # cas A : (p,q)∈p — reconstruction directe
    h_a = N.assume(appartient(cpl, vp))
    impA = N.loi_deduction(appartient(cpl, vp),
                           _reconstruire(vz, vp, vX, z_eq, pb_X, h_a))
    # cas B : (p,q)∈S — pb=x donc x∈X, contredit ¬(x∈X) ; ex falso encodé-∨
    h_s = N.assume(appartient(cpl, S))
    eq_cpl = N.modus_ponens(h_s, equivalence_avant(singleton_membre(cpl, cxv)))
    comp = N.modus_ponens(eq_cpl,
                          couple_egal_implique_composantes(vpb, vqb, vx, vv))
    x_X = N.modus_ponens(pb_X, equivalence_avant(N.modus_ponens(
        conjonction_elim_gauche(comp),                      # p=x
        N.s6(vpb, vx, "wxe", appartient(var("wxe"), vX)))))  # x∈X
    cible_B = appartient(vz, rD)
    z_in_B = N.modus_ponens(x_X, N.modus_ponens(h_notx,
        N.s2(non(appartient(vx, vX)), cible_B)))            # ¬A⇒(¬A∨C) == A⇒C
    impB = N.loi_deduction(appartient(cpl, S), z_in_B)
    z_in_pX = cas(disj, impA, impB)
    imp_ex = existe_elimination(existe_elimination(
        N.loi_deduction(corps_G, z_in_pX), "q"), "p")
    sub_GD0 = N.loi_deduction(appartient(vz, rG), N.modus_ponens(ex1, imp_ex))
    sub_GD = N.modus_ponens(N.generalisation("zre", sub_GD0), equivalence_avant(
        alpha_pour_tout("zre", "z", impl(appartient(vz, rG), appartient(vz, rD)))))

    # ── (⊇) z∈p|X ⇒ z∈(p∪S)|X ────────────────────────────────────────────────
    h_z2 = N.assume(appartient(vz, rD))
    ex2 = N.modus_ponens(h_z2, equivalence_avant(_inst_restriction(vp, vX, vz)))
    corps_D = _corps_restriction(vz, vp, vX)
    h_d = N.assume(corps_D)
    z_eq2 = conjonction_elim_gauche(conjonction_elim_gauche(h_d))
    pb_X2 = conjonction_elim_droite(conjonction_elim_gauche(h_d))
    pq_p = conjonction_elim_droite(h_d)                     # (p,q)∈p
    pq_pS2 = N.modus_ponens(
        N.modus_ponens(pq_p, N.s2(appartient(cpl, vp), appartient(cpl, S))),
        equivalence_arriere(membre_reunion_graphes(vp, S, cpl)))   # (p,q)∈p∪S
    z_in_G = _reconstruire(vz, pS, vX, z_eq2, pb_X2, pq_pS2)
    imp_ex2 = existe_elimination(existe_elimination(
        N.loi_deduction(corps_D, z_in_G), "q"), "p")
    sub_DG0 = N.loi_deduction(appartient(vz, rD), N.modus_ponens(ex2, imp_ex2))
    sub_DG = N.modus_ponens(N.generalisation("zre", sub_DG0), equivalence_avant(
        alpha_pour_tout("zre", "z", impl(appartient(vz, rD), appartient(vz, rG)))))

    # ── A1 : la double inclusion donne l'égalité ─────────────────────────────
    res = N.modus_ponens(conjonction_intro(sub_GD, sub_DG),
                         extensionnalite_appliquee(rG, rD))
    assert res.conclusion == egal(rG, rD), "restriction_reunion_singleton_hors : forme"
    assert list(res.hypotheses) == [non(appartient(vx, vX))], \
        "restriction_reunion_singleton_hors : hyps ≠ {¬(x∈X)}"
    return res


__all__ = ["restriction_reunion_singleton_hors"]
