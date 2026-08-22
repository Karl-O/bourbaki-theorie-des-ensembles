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


def x_hors_seg(G="Gsr", e="Esr", x="xsr"):
    """⊢ ¬( x ∈ seg(G,E,x) )                                    [CLOS, 0 hyp].

    Le point n'est jamais dans son segment OUVERT : x∈seg(x) donnerait x≠x
    (conjoint droit de l'axiome-segment), contredisant la réflexivité de =.
    Ex falso par l'encodage-∨ (¬A⇒(¬A∨C) == A⇒C), puis S1 replie A⇒¬A en ¬A."""
    vG, ve, vx = _t(G), _t(e), _t(x)
    segx = E.segment_extremite(vG, ve, vx)
    ax_seg = instancie(N.axiome(E.theorie_segment_extremite(),
                                E.axiome_segment_extremite()), vG)
    h = N.assume(appartient(vx, segx))
    corps = N.modus_ponens(h, equivalence_avant(
        instancie(instancie(instancie(ax_seg, ve), vx), vx)))
    x_ne_x = conjonction_elim_droite(corps)                 # ¬(x=x)
    cible = non(appartient(vx, segx))
    inner = N.modus_ponens(N.reflexivite(vx), N.modus_ponens(
        x_ne_x, N.s2(non(egal(vx, vx)), cible)))            # ¬(x∈seg x)  [sous h]
    imp = N.loi_deduction(appartient(vx, segx), inner)      # A ⇒ ¬A  ==  ¬A∨¬A
    res = N.modus_ponens(imp, N.s1(cible))                  # ¬A
    assert res.est_clos, "x_hors_seg : non clos"
    return res


def restriction_pleine(p="pes", u="ure"):
    """{ est_un_graphe(p) } ⊢ p | dom(p) = p                    [1 hyp honnête].

    La restriction au domaine ENTIER est l'identité : ⊆ est directe (le corps-
    témoin donne (pb,qb)∈p et z=(pb,qb)) ; ⊇ exige que z∈p SOIT un couple
    (est_un_graphe, hypothèse honnête), dont la 1ʳᵉ composante est dans dom p
    (couple_dans_dom) — on reconstruit le corps-témoin."""
    from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
        couple_dans_dom,
    )
    vp = _t(p)
    D = E.dom(vp)
    rP = E.restriction(vp, D)                               # p|dom p
    vz = var("zre")
    vpb, vqb = var("p"), var("q")
    cpl = E.couple(vpb, vqb)

    h_g = N.assume(E.est_un_graphe(vp))                     # p graphe   [HONNÊTE]

    # ── (⊆) z∈p|dom p ⇒ z∈p  (réécrire z=(pb,qb) dans (pb,qb)∈p) ────────────
    h_z1 = N.assume(appartient(vz, rP))
    ex1 = N.modus_ponens(h_z1, equivalence_avant(_inst_restriction(vp, D, vz)))
    corps = _corps_restriction(vz, vp, D)
    h_b = N.assume(corps)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(h_b))   # z=(pb,qb)
    pq_p = conjonction_elim_droite(h_b)                            # (pb,qb)∈p
    z_in_p = N.modus_ponens(pq_p, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, cpl, "wrp", appartient(var("wrp"), vp)))))  # z∈p
    imp_ex = existe_elimination(existe_elimination(
        N.loi_deduction(corps, z_in_p), "q"), "p")
    sub_1 = N.loi_deduction(appartient(vz, rP), N.modus_ponens(ex1, imp_ex))
    sub_G = N.modus_ponens(N.generalisation("zre", sub_1), equivalence_avant(
        alpha_pour_tout("zre", "z", impl(appartient(vz, rP), appartient(vz, vp)))))

    # ── (⊇) z∈p ⇒ z∈p|dom p  (z est un couple : est_un_graphe) ──────────────
    h_z2 = N.assume(appartient(vz, vp))
    z_couple = N.modus_ponens(h_z2, instancie(h_g, vz))     # (∃x)(∃y)(z=(x,y))
    vxb, vyb = var("x"), var("y")
    cxy = E.couple(vxb, vyb)
    h_e = N.assume(egal(vz, cxy))                           # témoins x, y
    xy_in_p = N.modus_ponens(h_z2, equivalence_avant(N.modus_ponens(
        h_e, N.s6(vz, cxy, "wrp", appartient(var("wrp"), vp)))))   # (x,y)∈p
    x_dom = couple_dans_dom(vp, vxb, vyb)                   # {(x,y)∈p} ⊢ x∈dom p
    x_dom = N.modus_ponens(xy_in_p, N.loi_deduction(appartient(cxy, vp), x_dom))
    # reconstruire le corps-témoin de p|dom p aux liants p/q via S6 (x,y)→liants :
    #   z=(x,y) ∧ x∈dom p ∧ (x,y)∈p  — puis S5 ×2 re-lie x→p, y→q.
    corps_xy = et(et(egal(vz, cxy), appartient(vxb, D)), appartient(cxy, vp))
    corps_prouve = conjonction_intro(conjonction_intro(h_e, x_dom), xy_in_p)
    corps_pq = _corps_restriction(vz, vp, D)                # liants p, q
    ex_q = N.modus_ponens(corps_prouve, N.s5(
        et(et(egal(vz, E.couple(vxb, vqb)), appartient(vxb, D)),
           appartient(E.couple(vxb, vqb), vp)), vyb, "q"))  # (∃q)(… x …)
    ex_pq = N.modus_ponens(ex_q, N.s5(existe("q", corps_pq), vxb, "p"))
    z_in_rP = N.modus_ponens(ex_pq, equivalence_arriere(_inst_restriction(vp, D, vz)))
    imp_ex2 = existe_elimination(existe_elimination(
        N.loi_deduction(egal(vz, cxy), z_in_rP), "y"), "x")
    z_in_rP2 = N.modus_ponens(z_couple, imp_ex2)
    sub_2 = N.loi_deduction(appartient(vz, vp), z_in_rP2)
    sub_D = N.modus_ponens(N.generalisation("zre", sub_2), equivalence_avant(
        alpha_pour_tout("zre", "z", impl(appartient(vz, vp), appartient(vz, rP)))))

    res = N.modus_ponens(conjonction_intro(sub_G, sub_D),
                         extensionnalite_appliquee(rP, vp))
    assert res.conclusion == egal(rP, vp), "restriction_pleine : forme"
    assert list(res.hypotheses) == [E.est_un_graphe(vp)], "restriction_pleine : hyps"
    return res


__all__ = ["restriction_reunion_singleton_hors", "x_hors_seg", "restriction_pleine"]
