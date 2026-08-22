# -*- coding: utf-8 -*-
"""§III.2.2 — R5'c (U2/U3) : LE DOMAINE DE LA RÉUNION ⋃Dfam_rec(x).

🎯 CIBLES :

    dom_union_inclus_seg  :  { bo }          ⊢  dom(⋃Dfam_rec(x)) ⊂ seg(x)
    seg_inclus_dom_union  :  { antécédent }  ⊢  seg(x) ⊂ dom(⋃Dfam_rec(x))
    dom_union_rec         :  { bo, antécédent } ⊢ dom(⋃Dfam_rec(x)) = seg(x)

où l'ANTÉCÉDENT est la couverture-AMBIANTE des y<x (l'hypothèse d'induction
de l'hérédité R5') :

    antecedent_couverture_rec := (∀yaa)( yaa∈seg(x) ⇒
        (∃paa)( paa∈𝔓(E×V) ∧ est_essai_rec(paa, yaa) ) )

⊆ : un z du domaine vient d'un couple (z,w) d'un membre p (essai d'un y<x) ;
z∈dom p = dom_essai(y) donne z<y ou z=y, et la transitivité stricte conclut
z<x (patron CASE A/B de couverture_segment_realise).
⊇ : z<x est couvert (antécédent) par un essai paa AMBIANT — paa∈Dfam_rec(x)
avec z lui-même pour témoin S5, et (z, paa(z)) ∈ paa ⊂ ⋃D.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, pourtout, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie, cas,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, alpha_pour_tout,
)
from bourbaki.ii_theorie_des_ensembles.ii_2_couples.ii_2_1_definition_couples.ensembles_couples import singleton_membre
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    _instance_reunion, extensionnalite_appliquee,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_fonctions import (
    valeur_dans_graphe,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    couple_dans_dom,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, _inst_union_famille, _membre_dans_union,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_seg_transitif import (
    seg_transitif_strict,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_coincidence_famille import (
    point_dans_dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_famille_rec import (
    Dfam_rec, membre_Dfam_rec,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def couvert_essai_rec_amb(vh, G, e, V="Vval", p="paa"):
    """couvert[y] := (∃paa)( paa∈𝔓(E×V) ∧ est_essai_rec(paa, y) )  — AMBIANT."""
    vp = var(p)
    return lambda y: existe(p, et(appartient(vp, ambiant(e, V)),
                                  est_essai_rec(vp, vh, _t(G), _t(e), y)))


def antecedent_couverture_rec(vh, G, e, x, V="Vval", y="yaa", p="paa"):
    """(∀yaa)( yaa∈seg(x) ⇒ couvert[yaa] )  — l'hypothèse d'induction R5'."""
    vy = var(y)
    segx = E.segment_extremite(_t(G), _t(e), _t(x))
    return pourtout(y, impl(appartient(vy, segx),
                            couvert_essai_rec_amb(vh, G, e, V, p)(vy)))


def dom_union_inclus_seg(vh, G="Gsr", e="Esr", x="xsr", V="Vval"):
    """U2 : { bo } ⊢ dom(⋃Dfam_rec(x)) ⊂ seg(x)               [1 hyp honnête]."""
    vG, ve, vx = _t(G), _t(e), _t(x)
    D = Dfam_rec(vG, ve, vx, V)
    U = union_famille(D)
    segx = E.segment_extremite(vG, ve, vx)
    vz, vw, vpun, vy = var("zdu"), var("wdu"), var("punion"), var("yDr")

    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    h_z = N.assume(appartient(vz, E.dom(U)))
    ex_w = N.modus_ponens(
        N.modus_ponens(h_z, equivalence_avant(instancie(instancie(ax_dom, U), vz))),
        equivalence_avant(alpha_existe("y", "wdu",
                                       appartient(E.couple(vz, var("y")), U))))
    h_zw = N.assume(appartient(E.couple(vz, vw), U))
    ex_pun = N.modus_ponens(h_zw, equivalence_avant(
        _inst_union_famille(D, E.couple(vz, vw))))
    corps_pun = et(appartient(vpun, D), appartient(E.couple(vz, vw), vpun))
    h_pun = N.assume(corps_pun)
    pun_D = conjonction_elim_gauche(h_pun)
    zw_pun = conjonction_elim_droite(h_pun)
    sel = conjonction_elim_droite(N.modus_ponens(pun_D, equivalence_avant(
        membre_Dfam_rec(vh, G, e, vx, vpun, V, y="yDr"))))
    corps_y = et(appartient(vy, segx), est_essai_rec(vpun, vh, vG, ve, vy))
    h_y = N.assume(corps_y)
    y_seg = conjonction_elim_gauche(h_y)
    dom_pun = conjonction_elim_droite(conjonction_elim_gauche(
        conjonction_elim_droite(h_y)))                      # dom punion = dom_essai(yDr)
    z_dey = N.modus_ponens(
        _cut(zw_pun, appartient(E.couple(vz, vw), vpun),
             couple_dans_dom(vpun, vz, vw)),
        equivalence_avant(N.modus_ponens(dom_pun, N.s6(
            E.dom(vpun), dom_essai(vG, ve, vy), "wdz", appartient(vz, var("wdz"))))))
    disj = N.modus_ponens(z_dey, equivalence_avant(_instance_reunion(
        E.segment_extremite(vG, ve, vy), E.singleton(vy), vz)))
    # CAS A : z∈seg(yDr), yDr∈seg(x) — transitivité stricte
    h_a = N.assume(appartient(vz, E.segment_extremite(vG, ve, vy)))
    impA = N.loi_deduction(appartient(vz, E.segment_extremite(vG, ve, vy)),
        N.modus_ponens(conjonction_intro(y_seg, h_a),
                       seg_transitif_strict(G, e, x, "yDr", "zdu")))
    # CAS B : z=yDr ∈ seg(x)
    h_b = N.assume(appartient(vz, E.singleton(vy)))
    z_eq_y = N.modus_ponens(h_b, equivalence_avant(singleton_membre(vz, vy)))
    impB = N.loi_deduction(appartient(vz, E.singleton(vy)),
        N.modus_ponens(y_seg, equivalence_arriere(N.modus_ponens(
            z_eq_y, N.s6(vz, vy, "wdz", appartient(var("wdz"), segx))))))
    z_segx = cas(disj, impA, impB)
    r1 = N.modus_ponens(sel, existe_elimination(
        N.loi_deduction(corps_y, z_segx), "yDr"))
    r2 = N.modus_ponens(ex_pun, existe_elimination(
        N.loi_deduction(corps_pun, r1), "punion"))
    r3 = N.modus_ponens(ex_w, existe_elimination(
        N.loi_deduction(appartient(E.couple(vz, vw), U), r2), "wdu"))
    sub = N.loi_deduction(appartient(vz, E.dom(U)), r3)
    return N.modus_ponens(N.generalisation("zdu", sub), equivalence_avant(
        alpha_pour_tout("zdu", "z", impl(appartient(vz, E.dom(U)),
                                         appartient(vz, segx)))))


def seg_inclus_dom_union(vh, G="Gsr", e="Esr", x="xsr", V="Vval"):
    """U3 : { antécédent } ⊢ seg(x) ⊂ dom(⋃Dfam_rec(x))       [1 hyp honnête]."""
    vG, ve, vx = _t(G), _t(e), _t(x)
    D = Dfam_rec(vG, ve, vx, V)
    U = union_famille(D)
    segx = E.segment_extremite(vG, ve, vx)
    vz, vpa = var("zdu"), var("paa")
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    h_ant = N.assume(antecedent_couverture_rec(vh, G, e, x, V))
    h_zs = N.assume(appartient(vz, segx))
    cov_z = N.modus_ponens(h_zs, instancie(h_ant, vz))      # (∃paa)(amb ∧ essai(paa,z))
    corps_pa = et(appartient(vpa, ambiant(e, V)),
                  est_essai_rec(vpa, vh, vG, ve, vz))
    h_pa = N.assume(corps_pa)
    pa_amb = conjonction_elim_gauche(h_pa)
    essai_pa = conjonction_elim_droite(h_pa)
    func_pa = conjonction_elim_gauche(conjonction_elim_gauche(essai_pa))
    dom_pa = conjonction_elim_droite(conjonction_elim_gauche(essai_pa))
    # paa∈Dfam_rec(x) : ambiant + témoin S5 (yDr := z lui-même)
    inner = et(appartient(var("yDr"), segx),
               est_essai_rec(vpa, vh, vG, ve, var("yDr")))
    ex_yDr = N.modus_ponens(conjonction_intro(h_zs, essai_pa),
                            N.s5(inner, vz, "yDr"))
    pa_D = N.modus_ponens(conjonction_intro(pa_amb, ex_yDr), equivalence_arriere(
        membre_Dfam_rec(vh, G, e, vx, vpa, V, y="yDr")))
    # z∈dom paa  (le point est dans son dom_essai, Leibniz)
    z_dompa = N.modus_ponens(point_dans_dom_essai(G, e, "zdu"),
        equivalence_arriere(N.modus_ponens(dom_pa, N.s6(
            E.dom(vpa), dom_essai(vG, ve, vz), "wdz", appartient(vz, var("wdz"))))))
    # (z, paa(z)) ∈ paa ⊂ ⋃D, donc z∈dom(⋃D)
    ex_y0 = N.modus_ponens(z_dompa, equivalence_avant(
        instancie(instancie(ax_dom, vpa), vz)))
    zin = _cut(ex_y0, existe("y", appartient(E.couple(vz, var("y")), vpa)),
               _cut(func_pa, E.est_fonctionnel(vpa), valeur_dans_graphe(vpa, vz)))
    in_U = _membre_dans_union(D, vpa, E.couple(vz, E.valeur(vpa, vz)), pa_D, zin)
    ex_y2 = N.modus_ponens(in_U, N.s5(
        appartient(E.couple(vz, var("y")), U), E.valeur(vpa, vz), "y"))
    z_domU = N.modus_ponens(ex_y2, equivalence_arriere(
        instancie(instancie(ax_dom, U), vz)))
    r = N.modus_ponens(cov_z, existe_elimination(
        N.loi_deduction(corps_pa, z_domU), "paa"))
    sub = N.loi_deduction(appartient(vz, segx), r)
    return N.modus_ponens(N.generalisation("zdu", sub), equivalence_avant(
        alpha_pour_tout("zdu", "z", impl(appartient(vz, segx),
                                         appartient(vz, E.dom(U))))))


def dom_union_rec(vh, G="Gsr", e="Esr", x="xsr", V="Vval"):
    """🎯 U-dom : { bo, antécédent } ⊢ dom(⋃Dfam_rec(x)) = seg(x)   [2 hyps]."""
    vG, ve, vx = _t(G), _t(e), _t(x)
    U = union_famille(Dfam_rec(vG, ve, vx, V))
    segx = E.segment_extremite(vG, ve, vx)
    res = N.modus_ponens(
        conjonction_intro(dom_union_inclus_seg(vh, G, e, x, V),
                          seg_inclus_dom_union(vh, G, e, x, V)),
        extensionnalite_appliquee(E.dom(U), segx))
    assert res.conclusion == egal(E.dom(U), segx), "dom_union_rec : forme"
    assert len(res.hypotheses) == 2, "dom_union_rec : hyps ≠ 2"
    return res


__all__ = ["couvert_essai_rec_amb", "antecedent_couverture_rec",
           "dom_union_inclus_seg", "seg_inclus_dom_union", "dom_union_rec"]
