# -*- coding: utf-8 -*-
"""§III.6.3 — H2 (pas 1-2) : LE RÉSIDU D'INDUCTIVITÉ GARDÉ + LE CAS C=∅ PAR H1.

🎯 CIBLES (restructuration du résidu H2, plan DECISIONS 2026-08-22 20h10) :

    m_dans_frame_garde(E) :=
        (∀C)( ( chaîne(Γ𝔉,𝔉,C) ∧ ¬(C=∅) ) ⇒ (⋃S(C),⋃φ(C)) ∈ 𝔉(E) )
    — le NOUVEAU résidu, SATISFIABLE (l'ancien ∀C-nu échouait sur C=∅ :
      le recollement (∅,∅) devrait être « infini »).

    enonce_chaine_majoree_garde :
        { m_dans_frame_garde(E),  (∃x)(x∈𝔉(E)) }  ⊢  enonce_chaine_majoree(Γ𝔉,𝔉)
    — même conclusion que la v1 (frame_inductif_assemblage), mais sous le
      résidu gardé + H1 : tiers exclu sur C=∅ ; la chaîne vide est majorée
      par N'IMPORTE QUEL élément de 𝔉 (vacuité du ∀), fourni par H1.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, equivalence_avant,
    instancie, tiers_exclu, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    vide_sans_element,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    majorant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    chaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (
    _ex_falso,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair, frame_ordre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_inductivite import (
    enonce_chaine_majoree,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    temoin_majore_membre,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_inductif_assemblage import (
    m_dans_frame_formule, temoin_couple,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_maximal_clos import (
    residu_H1,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def m_dans_frame_garde(E_set="E", C="C", x="xmaj", y="y", z="z"):
    """Le résidu GARDÉ :  (∀C)( (chaîne(Γ𝔉,𝔉,C) ∧ C≠∅) ⇒ (⋃S,⋃φ)∈𝔉(E) )."""
    vE, vC = _t(E_set), var(C)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    return pourtout(C, impl(et(chaine(Gam, Fr, vC, x, y, z),
                               non(egal(vC, E.VIDE))),
                            m_dans_frame_formule(E_set, vC)))


def enonce_chaine_majoree_garde(E_set="E", C="C", m="m", x="xmaj", y="y", z="z"):
    """🎯 { m_dans_frame_garde(E), (∃x)(x∈𝔉(E)) } ⊢ enonce_chaine_majoree(Γ𝔉,𝔉)
       [2 hyps honnêtes — le résidu gardé et H1].

    Tiers exclu sur C=∅ : la chaîne vide est majorée par le témoin de H1
    (vacuité) ; la chaîne non vide par son recollement (résidu gardé), le
    reste du chemin étant celui de la v1 (temoin_majore_membre + cuts)."""
    vE, vC = _t(E_set), var(C)
    Gam, Fr = frame_ordre(vE), frame_pair(vE)
    mt = temoin_couple(vC)
    vx, vxm = var("x"), var(x)
    R = majorant(Gam, vC, var(m), Fr, x)                    # corps ouvert en m

    h_garde = N.assume(m_dans_frame_garde(E_set, C, x, y, z))   # [HONNÊTE]
    h_H1 = N.assume(residu_H1(E_set))                       # (∃x)(x∈𝔉)  [HONNÊTE]
    h_chaine = N.assume(chaine(Gam, Fr, vC, x, y, z))       # [déchargée plus bas]

    # ── cas A : C = ∅ — le témoin de H1 majore la chaîne vide (vacuité) ─────
    ha = N.assume(egal(vC, E.VIDE))
    h_w = N.assume(appartient(vx, Fr))                      # le témoin x∈𝔉
    h_xm = N.assume(appartient(vxm, vC))                    # xmaj∈C (absurde)
    xm_vide = N.modus_ponens(h_xm, equivalence_avant(N.modus_ponens(
        ha, N.s6(vC, E.VIDE, "wh2", appartient(vxm, var("wh2"))))))   # xmaj∈∅
    absurd = _ex_falso(xm_vide, vide_sans_element(x),
                       appartient(E.couple(vxm, vx), Gam))
    forall_vac = N.generalisation(x, N.loi_deduction(appartient(vxm, vC),
                                                     absurd))
    maj_A = conjonction_intro(h_w, forall_vac)              # majorant(Γ,C,x,𝔉)
    ex_m_A = N.modus_ponens(maj_A, N.s5(R, vx, m))          # (∃m)majorant
    ex_m_A = N.modus_ponens(h_H1, existe_elimination(
        N.loi_deduction(appartient(vx, Fr), ex_m_A), "x"))  # témoin H1 éliminé
    brA = N.loi_deduction(egal(vC, E.VIDE), ex_m_A)

    # ── cas B : C ≠ ∅ — le recollement (résidu gardé), chemin de la v1 ──────
    hb = N.assume(non(egal(vC, E.VIDE)))
    h_mFr = N.modus_ponens(conjonction_intro(h_chaine, hb),
                           instancie(h_garde, vC))          # (⋃S,⋃φ)∈𝔉
    C_inc_Fr = conjonction_elim_gauche(h_chaine)            # C⊂𝔉
    h_xC = N.assume(appartient(vxm, vC))
    x_in_Fr = N.modus_ponens(h_xC, instancie(C_inc_Fr, vxm))
    tmm = temoin_majore_membre(E_set, C, x)                 # (xmaj,m)∈Γ𝔉
    step = N.modus_ponens(x_in_Fr,
                          N.loi_deduction(appartient(vxm, Fr), tmm))
    step = N.modus_ponens(h_mFr,
                          N.loi_deduction(appartient(mt, Fr), step))
    forall_x = N.generalisation(x, N.loi_deduction(appartient(vxm, vC), step))
    maj_B = conjonction_intro(h_mFr, forall_x)
    ex_m_B = N.modus_ponens(maj_B, N.s5(R, mt, m))
    brB = N.loi_deduction(non(egal(vC, E.VIDE)), ex_m_B)

    # ── recollement des cas, décharge de la chaîne, généralisation ──────────
    conc = cas(tiers_exclu(egal(vC, E.VIDE)), brA, brB)     # (∃m)majorant
    impl_C = N.loi_deduction(chaine(Gam, Fr, vC, x, y, z), conc)
    res = N.generalisation(C, impl_C)

    cible = enonce_chaine_majoree(Gam, Fr, C, m, x, y, z)
    assert res.conclusion == cible, "enonce_chaine_majoree_garde : forme"
    assert set(res.hypotheses) == {m_dans_frame_garde(E_set, C, x, y, z),
                                   residu_H1(E_set)}, \
        "enonce_chaine_majoree_garde : hyps ≠ {garde, H1}"
    return res


__all__ = ["m_dans_frame_garde", "enonce_chaine_majoree_garde"]
