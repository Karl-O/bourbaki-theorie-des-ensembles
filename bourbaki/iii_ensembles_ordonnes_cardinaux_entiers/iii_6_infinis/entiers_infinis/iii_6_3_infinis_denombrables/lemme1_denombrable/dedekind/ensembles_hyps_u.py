# -*- coding: utf-8 -*-
"""§III.6.3 — D1c : LES QUATRE HYPOTHÈSES DE u := x ↦ h((x,0)) SOUS h_bij.

🎯 CIBLES (u := graphe_terme(E, x↦h((x,0))), x0 := h(m), m=(∅,1)) :

    dom_u_egal_E   :  ⊢ dom u = E                                    (CLOS)
    u_inclus_EE    :  { h_bij } ⊢ u ⊂ E×E
    hors_x0        :  { h_bij } ⊢ (∀t)( t∈E ⇒ ¬(u(t) = x0) )
    u_injective    :  { h_bij } ⊢ injective_dans(u, E)

L'argument : u(t) = h((t,0)) (valeur du graphe-terme) ; h est injective sur
W = E⊔{∅}, et les copies (t,0) / (∅,1) sont disjointes — une collision
forcerait 0 = 1 (projections du couple), contredisant ¬(1=0).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, non, impl, appartient, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination,
)
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import (
    couple_egal_implique_composantes,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_2_produit_deux_ensembles.ensembles_produit import (
    couple_dans_produit_ssi,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_6_fonction_terme.ensembles_fonction_terme import (
    _inst_axiome,
)
from bourbaki.ii_theorie_des_ensembles.ii_4_reunion_intersection_famille.ii_4_recollement_somme.ensembles_somme_disjointe import (
    ZERO, UN, injection_gauche_dans_somme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_3_somme.ensembles_somme_equipotence import (
    _neg_un_egal_zero,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor.ensembles_cantor import (
    graphe_terme_valeur, graphe_terme_domaine,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.definitions_cardinaux.ensembles_cardinaux_consequences import (
    _ex_falso,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_carte_egale import (
    SINGZ,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_6_infinis.entiers_infinis.iii_6_3_infinis_denombrables.lemme1_denombrable.dedekind.ensembles_donnees_dedekind import (
    MARQUEUR, x0_dedekind, u_dedekind, marqueur_dans_W,
    _couple_valeur, _valeur_dans_E, _extraire_bijection, _cut,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _T_de(vh, x="xdk"):
    """Le terme x ↦ h((x, 0)) (variable libre x)."""
    return E.valeur(vh, E.couple(var(x), ZERO))


def dom_u_egal_E(h="hdk", e="Eld"):
    """⊢ dom u = E   (graphe_terme_domaine ; CLOS)."""
    vh, ve = _t(h), _t(e)
    res = graphe_terme_domaine(ve, _T_de(vh), "xdk", "y", "z")
    assert res.conclusion == egal(E.dom(u_dedekind(vh, ve)), ve), \
        "dom_u_egal_E : forme"
    assert res.est_clos, "dom_u_egal_E : non clos"
    return res


def _u_valeur(vh, ve, tname):
    """{t∈E} ⊢ u(t) = h((t, 0))   (valeur du graphe-terme au point t)."""
    return graphe_terme_valeur(ve, _T_de(vh), tname, "xdk", "y")


def u_inclus_EE(h="hdk", e="Eld", z="z"):
    """🎯 D1c : { h_bij } ⊢ u ⊂ E×E   [1 hyp].

    z∈u se déplie (axiome du graphe-terme) en (∃xdk)(∃y)(z=(xdk,y) ∧ xdk∈E ∧
    y=h((xdk,0))) ; sous le corps, y∈E (l'image de h vit dans E) et z∈E×E."""
    vh, ve, W, func, dom_h, inj_h, img = _extraire_bijection(h, e)
    U = u_dedekind(vh, ve)
    T = _T_de(vh)
    vz, vx, vy = var(z), var("xdk"), var("y")
    EE = E.produit(ve, ve)

    car = _inst_axiome(ve, T, vz, "xdk", "y")               # z∈u ⇔ (∃xdk)(∃y)(…)
    corps = et(et(egal(vz, E.couple(vx, vy)), appartient(vx, ve)),
               egal(vy, T))
    h_c = N.assume(corps)
    z_eq = conjonction_elim_gauche(conjonction_elim_gauche(h_c))
    x_in = conjonction_elim_droite(conjonction_elim_gauche(h_c))
    y_eq = conjonction_elim_droite(h_c)                     # y = h((xdk,0))
    t0_in_W = N.modus_ponens(x_in, injection_gauche_dans_somme(vx, ve, SINGZ))
    T_in_E = _valeur_dans_E(vh, W, ve, E.couple(vx, ZERO), func, dom_h, img,
                            t0_in_W)                        # h((xdk,0))∈E
    y_in = N.modus_ponens(T_in_E, equivalence_arriere(N.modus_ponens(
        y_eq, N.s6(vy, T, "wdk", appartient(var("wdk"), ve)))))   # y∈E
    cpl_in = N.modus_ponens(conjonction_intro(x_in, y_in),
        equivalence_arriere(couple_dans_produit_ssi(vx, vy, ve, ve)))
    z_in = N.modus_ponens(cpl_in, equivalence_arriere(N.modus_ponens(
        z_eq, N.s6(vz, E.couple(vx, vy), "wdk",
                   appartient(var("wdk"), EE)))))           # z∈E×E
    imp = N.loi_deduction(corps, z_in)
    ex2 = existe_elimination(imp, "y")
    ex1 = existe_elimination(ex2, "xdk")
    z_final = N.modus_ponens(N.modus_ponens(
        N.assume(appartient(vz, U)), equivalence_avant(car)), ex1)
    res = N.generalisation(z, N.loi_deduction(appartient(vz, U), z_final))
    assert res.conclusion == inclus(U, EE, z), "u_inclus_EE : forme"
    assert len(res.hypotheses) == 1, "u_inclus_EE : hyps ≠ 1"
    return res


def _collision_copies(vh, ve, inj_h, vt, t0_in_W, h_eq, cible):
    """{(t,0)∈W, h((t,0))=h(m), inj_h} ⊢ cible — la collision force 1=0, absurde.

    L'injectivité gardée de h donne (t,0)=(∅,1) ; les projections (couple)
    donnent 0=1 ; symétrie puis ¬(1=0) concluent par ex falso."""
    t0 = E.couple(vt, ZERO)                                 # le couple (t,0)
    inj_inst = instancie(instancie(inj_h, t0), MARQUEUR)
    egal_couples = N.modus_ponens(conjonction_intro(
        conjonction_intro(t0_in_W, marqueur_dans_W(ve)), h_eq), inj_inst)
    comp = N.modus_ponens(egal_couples,
        couple_egal_implique_composantes(vt, ZERO, ZERO, UN))
    un_eq_zero = N.modus_ponens(conjonction_elim_droite(comp),
                                symetrie(ZERO, UN))         # 1 = 0
    return _ex_falso(un_eq_zero, _neg_un_egal_zero(), cible)


def hors_x0(h="hdk", e="Eld", t="thi"):
    """🎯 D1c : { h_bij } ⊢ (∀t)( t∈E ⇒ ¬(u(t) = x0) )   [1 hyp]."""
    vh, ve, W, func, dom_h, inj_h, img = _extraire_bijection(h, e)
    vt = var(t)
    ut, x0 = E.valeur(u_dedekind(vh, ve), vt), x0_dedekind(vh)
    cible = non(egal(ut, x0))

    h_t = N.assume(appartient(vt, ve))
    u_val = _cut(h_t, appartient(vt, ve), _u_valeur(vh, ve, t))  # u(t)=h((t,0))
    t0_in_W = N.modus_ponens(h_t, injection_gauche_dans_somme(vt, ve, SINGZ))
    h_abs = N.assume(egal(ut, x0))                          # u(t) = x0 (absurde)
    h_eq = composer_egalites(N.modus_ponens(
        u_val, symetrie(ut, E.valeur(vh, E.couple(vt, ZERO)))), h_abs)
    inner = _collision_copies(vh, ve, inj_h, vt, t0_in_W, h_eq, cible)
    res_t = N.modus_ponens(N.loi_deduction(egal(ut, x0), inner), N.s1(cible))
    res = N.generalisation(t, N.loi_deduction(appartient(vt, ve), res_t))
    assert res.conclusion == pourtout(t, impl(appartient(vt, ve), cible)), \
        "hors_x0 : forme"
    assert len(res.hypotheses) == 1, "hors_x0 : hyps ≠ 1"
    return res


def u_injective(h="hdk", e="Eld"):
    """🎯 D1c : { h_bij } ⊢ injective_dans(u, E)   [1 hyp].

    u(t)=u(t') transporte sur h ; h injective sur W donne (t,0)=(t',0) ;
    la composante gauche conclut t=t'."""
    vh, ve, W, func, dom_h, inj_h, img = _extraire_bijection(h, e)
    U = u_dedekind(vh, ve)
    vu_, vup = var("u"), var("up")
    ant = et(et(appartient(vu_, ve), appartient(vup, ve)),
             egal(E.valeur(U, vu_), E.valeur(U, vup)))
    h_ant = N.assume(ant)
    u_in = conjonction_elim_gauche(conjonction_elim_gauche(h_ant))
    up_in = conjonction_elim_droite(conjonction_elim_gauche(h_ant))
    coll = conjonction_elim_droite(h_ant)
    val_u = _cut(u_in, appartient(vu_, ve), _u_valeur(vh, ve, "u"))
    val_up = _cut(up_in, appartient(vup, ve), _u_valeur(vh, ve, "up"))
    hu, hup = E.valeur(vh, E.couple(vu_, ZERO)), E.valeur(vh, E.couple(vup, ZERO))
    h_eq = composer_egalites(composer_egalites(N.modus_ponens(
        val_u, symetrie(E.valeur(U, vu_), hu)), coll), val_up)   # h((u,0))=h((up,0))
    t0, t0p = E.couple(vu_, ZERO), E.couple(vup, ZERO)
    in_W = N.modus_ponens(u_in, injection_gauche_dans_somme(vu_, ve, SINGZ))
    inp_W = N.modus_ponens(up_in, injection_gauche_dans_somme(vup, ve, SINGZ))
    egal_couples = N.modus_ponens(conjonction_intro(
        conjonction_intro(in_W, inp_W), h_eq),
        instancie(instancie(inj_h, t0), t0p))               # (u,0)=(up,0)
    res_uu = conjonction_elim_gauche(N.modus_ponens(egal_couples,
        couple_egal_implique_composantes(vu_, ZERO, vup, ZERO)))  # u=up
    res = N.generalisation("u", N.generalisation("up",
        N.loi_deduction(ant, res_uu)))
    assert res.conclusion == E.injective_dans(U, ve), "u_injective : forme"
    assert len(res.hypotheses) == 1, "u_injective : hyps ≠ 1"
    return res


__all__ = ["dom_u_egal_E", "u_inclus_EE", "hors_x0", "u_injective"]
