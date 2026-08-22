# -*- coding: utf-8 -*-
"""§III.2.2 — R4'b : COMPOSITION DES RESTRICTIONS ((p|A)|B = p|B sous B⊂A).

🎯 CIBLE (une hypothèse honnête) :

    composition_restrictions :  { B ⊂ A }  ⊢  (p|A)|B = p|B

Brique de la restriction d'essai (R4'a) : l'équation de p|dom_essai(y) en z lit
(p|D)|seg(z), qui doit être p|seg(z) — la restriction intermédiaire D est
transparente dès que seg(z) ⊂ D.

PREUVE (double inclusion, témoins aux liants « p »/« q » de l'axiome) :
  ⊆  z∈(p|A)|B : témoins z=(pb,qb), pb∈B, (pb,qb)∈p|A ; le niveau-couple
     (_couple_restriction) extrait (pb,qb)∈p ; on reconstruit pour p|B.
  ⊇  z∈p|B : témoins z=(pb,qb), pb∈B, (pb,qb)∈p ; pb∈A (B⊂A instanciée),
     donc (pb,qb)∈p|A (niveau-couple, sens ⇐) ; on reconstruit pour (p|A)|B.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, impl, appartient, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_pour_tout,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_briques import (
    _inst_restriction,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
    _couple_restriction,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_essai import (
    _corps_restriction, _reconstruire,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _elimine_temoins(source_form, ex_thm, corps, cible_thm):
    """Élimine les témoins p,q : de (∃p)(∃q)corps ⇒ cible, conclut cible."""
    imp = existe_elimination(existe_elimination(
        N.loi_deduction(corps, cible_thm), "q"), "p")
    return N.modus_ponens(ex_thm, imp)


def composition_restrictions(p="pcr", A="Acr", B="Bcr"):
    """{ B ⊂ A } ⊢ (p|A)|B = p|B                              [1 hyp honnête]."""
    vp, vA, vB = _t(p), _t(A), _t(B)
    pA = E.restriction(vp, vA)
    rG = E.restriction(pA, vB)                              # (p|A)|B
    rD = E.restriction(vp, vB)                              # p|B
    vz = var("zcr")
    vpb, vqb = var("p"), var("q")
    cpl = E.couple(vpb, vqb)

    h_sub = N.assume(inclus(vB, vA))                        # B ⊂ A     [HONNÊTE]

    # ── (⊆) z∈(p|A)|B ⇒ z∈p|B ────────────────────────────────────────────────
    h_z1 = N.assume(appartient(vz, rG))
    ex1 = N.modus_ponens(h_z1, equivalence_avant(_inst_restriction(pA, vB, vz)))
    corps_G = _corps_restriction(vz, pA, vB)
    h_b = N.assume(corps_G)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(h_b))   # z=(pb,qb)
    pb_B = conjonction_elim_droite(conjonction_elim_gauche(h_b))   # pb∈B
    pq_pA = conjonction_elim_droite(h_b)                           # (pb,qb)∈p|A
    pq_p = conjonction_elim_droite(N.modus_ponens(pq_pA,
        equivalence_avant(_couple_restriction(vp, vA, vpb, vqb))))  # (pb,qb)∈p
    z_in_D = _reconstruire(vz, vp, vB, z_eq, pb_B, pq_p)           # z∈p|B
    sub_1 = N.loi_deduction(appartient(vz, rG),
                            _elimine_temoins(corps_G, ex1, corps_G, z_in_D))
    sub_G = N.modus_ponens(N.generalisation("zcr", sub_1), equivalence_avant(
        alpha_pour_tout("zcr", "z", impl(appartient(vz, rG), appartient(vz, rD)))))

    # ── (⊇) z∈p|B ⇒ z∈(p|A)|B ────────────────────────────────────────────────
    h_z2 = N.assume(appartient(vz, rD))
    ex2 = N.modus_ponens(h_z2, equivalence_avant(_inst_restriction(vp, vB, vz)))
    corps_D = _corps_restriction(vz, vp, vB)
    h_d = N.assume(corps_D)
    z_eq2 = conjonction_elim_gauche(conjonction_elim_gauche(h_d))
    pb_B2 = conjonction_elim_droite(conjonction_elim_gauche(h_d))
    pq_p2 = conjonction_elim_droite(h_d)                           # (pb,qb)∈p
    pb_A = N.modus_ponens(pb_B2, instancie(h_sub, vpb))            # pb∈A
    pq_pA2 = N.modus_ponens(conjonction_intro(pb_A, pq_p2),
        equivalence_arriere(_couple_restriction(vp, vA, vpb, vqb)))  # (pb,qb)∈p|A
    z_in_G = _reconstruire(vz, pA, vB, z_eq2, pb_B2, pq_pA2)       # z∈(p|A)|B
    sub_2 = N.loi_deduction(appartient(vz, rD),
                            _elimine_temoins(corps_D, ex2, corps_D, z_in_G))
    sub_D = N.modus_ponens(N.generalisation("zcr", sub_2), equivalence_avant(
        alpha_pour_tout("zcr", "z", impl(appartient(vz, rD), appartient(vz, rG)))))

    res = N.modus_ponens(conjonction_intro(sub_G, sub_D),
                         extensionnalite_appliquee(rG, rD))
    assert res.conclusion == egal(rG, rD), "composition_restrictions : forme"
    assert list(res.hypotheses) == [inclus(vB, vA)], "composition_restrictions : hyps"
    return res


__all__ = ["composition_restrictions"]
