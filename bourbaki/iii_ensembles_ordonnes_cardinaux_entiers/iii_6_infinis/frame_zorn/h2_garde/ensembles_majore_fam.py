# -*- coding: utf-8 -*-
"""§III.6.3 — H2 : LE TÉMOIN-MAJORANT AVEC LA RÉUNION DE FAMILLE.

🎯 CIBLE (m' := ( ⋃S(C), ⋃𝔇(C) ) où 𝔇(C) = pr₂⟨C⟩) :

    majore_fam :  { p∈C, p∈𝔉(E), m'∈𝔉(E) }  ⊢  ( p, m' ) ∈ Γ𝔉(E)

C'est `temoin_majore_membre` avec la seconde composante du témoin changée :
⋃𝔇 (réunion de la famille des graphes) au lieu de ⋃φ (seconde projection de
la chaîne).  L'unique différence de preuve est l'inclusion pr₂(p)⊂⋃𝔇, que
`inclus_dans_union_fam` fournit — ce qui évite entièrement l'égalité des deux
unions, restée en chantier (leçon 15).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, inclus, pourtout,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, equivalence_avant,
    equivalence_arriere, instancie, tiers_exclu, cas,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_inductivite import (
    enonce_chaine_majoree, frame_inductif,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.outil_alpha_bridge import (
    alpha_bridge,
)
from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import existe
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_1_relations_ordre.ordre_treillis.ensembles_ordre_relation import (
    est_ordre, element_maximal,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.zorn_zermelo.ensembles_zorn import (
    est_inductif,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    maximal_pair_existe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_a_maximal import (
    _frame_ordre_xyz_named, _frame_ordre_xyz,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_maximal_clos import (
    residu_H1,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_projections import (
    projection_premiere, projection_seconde,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.chaine_recollement.ensembles_chaine_temoin_abstrait import (
    union_premiere, membre_donne_inclus_premiere,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
    frame_pair,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.ensembles_frame_ordre_axiome import (
    frame_ordre_membre_t,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.frame_zorn.h2_garde.ensembles_fam_chaine import (
    famille_de_chaine, inclus_dans_union_fam,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def temoin_fam(C):
    """m'(C) := ( ⋃S(C), ⋃𝔇(C) ) — le témoin-majorant version famille."""
    vC = _t(C)
    return E.couple(union_premiere(vC), union_famille(famille_de_chaine(vC)))


def majore_fam(E_set="E", C="Cch", p="pmemb"):
    """🎯 { p∈C, p∈𝔉(E), m'∈𝔉(E) } ⊢ ( p, m' ) ∈ Γ𝔉(E)   [3 hyps honnêtes].

    Patron de temoin_majore_membre : l'ordre d'extension demande les deux
    inclusions de projections ; la première vient de l'amont, la seconde de
    inclus_dans_union_fam."""
    vE, vC, vp = _t(E_set), _t(C), _t(p)
    US = union_premiere(vC)
    UD = union_famille(famille_de_chaine(vC))
    m = E.couple(US, UD)
    Fr = frame_pair(vE)
    pr1p, pr2p = E.pr1(vp), E.pr2(vp)

    incl1 = membre_donne_inclus_premiere(C, p)              # {p∈C} ⊢ pr₁p⊂⋃S
    incl2 = inclus_dans_union_fam(C, p)                     # {p∈C} ⊢ pr₂p⊂⋃𝔇

    #   identification des projections du couple-témoin (formes PROUVÉES)
    pp = N.generalisation("u", N.generalisation("v", projection_premiere("u", "v")))
    e1 = instancie(instancie(pp, US), UD)                   # pr₁(m')=⋃S
    ps = N.generalisation("u", N.generalisation("v", projection_seconde("u", "v")))
    e2 = instancie(instancie(ps, US), UD)                   # pr₂(m')=⋃𝔇
    pr1m = e1.conclusion.termes[0]
    pr2m = e2.conclusion.termes[0]

    #   transport des inclusions vers les projections du témoin
    eq1 = N.modus_ponens(e1, symetrie(pr1m, US))            # ⋃S = pr₁(m')
    incl1_m = N.modus_ponens(incl1, equivalence_avant(N.modus_ponens(
        eq1, N.s6(US, pr1m, "wmf", inclus(pr1p, var("wmf"))))))
    eq2 = N.modus_ponens(e2, symetrie(pr2m, UD))            # ⋃𝔇 = pr₂(m')
    incl2_m = N.modus_ponens(incl2, equivalence_avant(N.modus_ponens(
        eq2, N.s6(UD, pr2m, "wmf", inclus(pr2p, var("wmf"))))))

    h_pFr = N.assume(appartient(vp, Fr))                    # p∈𝔉  [HONNÊTE]
    h_mFr = N.assume(appartient(m, Fr))                     # m'∈𝔉 [HONNÊTE]
    corps = conjonction_intro(conjonction_intro(
        conjonction_intro(h_pFr, h_mFr), incl1_m), incl2_m)
    res = N.modus_ponens(corps, equivalence_arriere(
        frame_ordre_membre_t(vE, vp, m)))

    assert res.conclusion == appartient(E.couple(vp, m), _ordre(vE)), \
        "majore_fam : forme"
    assert len(res.hypotheses) == 3, "majore_fam : hyps ≠ 3"
    return res


def _ordre(vE):
    """Γ𝔉(E) — le graphe d'ordre d'extension du frame."""
    from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.hessenberg.coeur.ensembles_hessenberg_hard import (
        frame_ordre,
    )
    return frame_ordre(vE)


def residu_fam(E_set="E", C="C", x="xmaj", y="y", z="z"):
    """Le résidu GARDÉ, version famille :
       (∀C)( ( chaîne(Γ𝔉,𝔉,C) ∧ C≠∅ ) ⇒ ( ⋃S(C), ⋃𝔇(C) ) ∈ 𝔉(E) )."""
    vE, vC = _t(E_set), var(C)
    Gam, Fr = _ordre(vE), frame_pair(vE)
    return pourtout(C, impl(et(chaine(Gam, Fr, vC, x, y, z),
                               non(egal(vC, E.VIDE))),
                            appartient(temoin_fam(vC), Fr)))


def chaine_majoree_fam(E_set="E", C="C", m="m", x="xmaj", y="y", z="z"):
    """🎯 { residu_fam(E), (∃x)(x∈𝔉(E)) } ⊢ enonce_chaine_majoree(Γ𝔉, 𝔉)
       [2 hyps honnêtes].

    Réplique de enonce_chaine_majoree_garde avec le témoin (⋃S,⋃𝔇) : chaîne
    vide majorée par le témoin de H1 (vacuité) ; chaîne non vide majorée par
    son recollement, l'ordre venant de majore_fam."""
    vE, vC = _t(E_set), var(C)
    Gam, Fr = _ordre(vE), frame_pair(vE)
    mt = temoin_fam(vC)
    vx, vxm = var("x"), var(x)
    R = majorant(Gam, vC, var(m), Fr, x)

    h_res = N.assume(residu_fam(E_set, C, x, y, z))         # [HONNÊTE]
    h_H1 = N.assume(residu_H1(E_set))                       # (∃x)(x∈𝔉)  [HONNÊTE]
    h_chaine = N.assume(chaine(Gam, Fr, vC, x, y, z))

    #   cas A : C = ∅ — vacuité, majorée par le témoin de H1
    ha = N.assume(egal(vC, E.VIDE))
    h_w = N.assume(appartient(vx, Fr))
    h_xm = N.assume(appartient(vxm, vC))
    xm_vide = N.modus_ponens(h_xm, equivalence_avant(N.modus_ponens(
        ha, N.s6(vC, E.VIDE, "wmj", appartient(vxm, var("wmj"))))))
    absurd = _ex_falso(xm_vide, vide_sans_element(x),
                       appartient(E.couple(vxm, vx), Gam))
    forall_vac = N.generalisation(x, N.loi_deduction(appartient(vxm, vC), absurd))
    ex_m_A = N.modus_ponens(conjonction_intro(h_w, forall_vac), N.s5(R, vx, m))
    ex_m_A = N.modus_ponens(h_H1, existe_elimination(
        N.loi_deduction(appartient(vx, Fr), ex_m_A), "x"))
    brA = N.loi_deduction(egal(vC, E.VIDE), ex_m_A)

    #   cas B : C ≠ ∅ — le recollement majore, via majore_fam
    hb = N.assume(non(egal(vC, E.VIDE)))
    h_mFr = N.modus_ponens(conjonction_intro(h_chaine, hb),
                           instancie(h_res, vC))            # m'∈𝔉
    C_inc = conjonction_elim_gauche(h_chaine)               # C⊂𝔉
    h_xC = N.assume(appartient(vxm, vC))
    x_in_Fr = N.modus_ponens(h_xC, instancie(C_inc, vxm))
    ordre_xm = majore_fam(E_set, C, x)                      # (xmaj,m')∈Γ𝔉
    step = N.modus_ponens(x_in_Fr,
                          N.loi_deduction(appartient(vxm, Fr), ordre_xm))
    step = N.modus_ponens(h_mFr, N.loi_deduction(appartient(mt, Fr), step))
    forall_x = N.generalisation(x, N.loi_deduction(appartient(vxm, vC), step))
    ex_m_B = N.modus_ponens(conjonction_intro(h_mFr, forall_x), N.s5(R, mt, m))
    brB = N.loi_deduction(non(egal(vC, E.VIDE)), ex_m_B)

    conc = cas(tiers_exclu(egal(vC, E.VIDE)), brA, brB)
    res = N.generalisation(C, N.loi_deduction(
        chaine(Gam, Fr, vC, x, y, z), conc))
    assert res.conclusion == enonce_chaine_majoree(Gam, Fr, C, m, x, y, z),         "chaine_majoree_fam : forme"
    assert set(res.hypotheses) == {residu_fam(E_set, C, x, y, z),
                                   residu_H1(E_set)},         "chaine_majoree_fam : hyps ≠ {residu_fam, H1}"
    return res


def maximal_fam(E_set="E"):
    """🎯🎯🎯 { residu_fam(E), (∃x)(x∈𝔉(E)) }
       ⊢ (∃m) element_maximal( Γ𝔉(E), 𝔉(E), m )   [2 hyps honnêtes].

    Zorn appliqué au poset du frame, avec l'énoncé de chaîne majorée fourni
    par la version famille.  Les DEUX hypothèses restantes sont : le résidu
    du recollement (chaîne non vide) et H1 — ce dernier étant DÉJÀ CERTIFIÉ
    sous « E infini » (h1_decharge)."""
    vE = _t(E_set)
    Gam, Fr = _ordre(vE), frame_pair(vE)
    fi = frame_inductif(E_set, "C", "m", "xmaj", "y", "z")
    ordre = _frame_ordre_xyz_named(E_set, "xmaj", "y", "z")
    fi = N.modus_ponens(ordre, N.loi_deduction(
        est_ordre(Gam, Fr, "xmaj", "y", "z"), fi))
    ecm = chaine_majoree_fam(E_set)
    fi = N.modus_ponens(ecm, N.loi_deduction(
        enonce_chaine_majoree(Gam, Fr, "C", "m", "xmaj", "y", "z"), fi))
    induct = alpha_bridge(fi, est_inductif(Gam, Fr, "C", "m", "x", "y", "z"))
    h_nv = N.assume(residu_H1(E_set))
    res = N.modus_ponens(conjonction_intro(conjonction_intro(
        _frame_ordre_xyz(E_set), induct), h_nv), maximal_pair_existe(E_set))
    assert res.conclusion == existe("m", element_maximal(
        Gam, Fr, var("m"), "x")), "maximal_fam : forme"
    assert set(res.hypotheses) == {residu_fam(E_set), residu_H1(E_set)},         "maximal_fam : hyps ≠ {residu_fam, H1}"
    return res


__all__ = ["temoin_fam", "majore_fam", "residu_fam", "chaine_majoree_fam",
           "maximal_fam"]
