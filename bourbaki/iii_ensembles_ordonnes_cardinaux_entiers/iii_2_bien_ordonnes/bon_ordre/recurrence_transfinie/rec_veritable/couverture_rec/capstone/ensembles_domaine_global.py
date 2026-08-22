# -*- coding: utf-8 -*-
"""§III.2.2 — R7' (étape 2) : LE DOMAINE DE LA SOLUTION GLOBALE EST E.

🎯 CIBLES (f := ⋃Dglob_rec(G,E,V)) :

    dom_f_inclus_E :  ⊢ dom f ⊂ E                              [CLOS, 0 hyp]
    E_inclus_dom_f :  { bo, regle_dans_V }  ⊢  E ⊂ dom f
    dom_f_egal_E   :  { bo, regle_dans_V }  ⊢  dom f = E

⊆ : tout z du domaine vient d'un membre, essai d'un y∈E, et z∈dom_essai(y)⊂E.
⊇ : la COUVERTURE TOTALE (R6') fournit à chaque z∈E son essai ambiant paa,
membre de la famille globale (témoin S5 : z lui-même), et (z, paa(z)) ∈ f.

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, existe, inclus,
)
from bourbaki.i_description_mathematique_formelle.i_2_theoremes.noyau import noyau_abrege as N
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes import ensembles_abrege as E

from bourbaki.i_description_mathematique_formelle.i_2_theoremes.tactiques.tactiques_abrege2 import (
    conjonction_intro, conjonction_elim_gauche, conjonction_elim_droite,
    equivalence_avant, equivalence_arriere, instancie,
)
from bourbaki.i_description_mathematique_formelle.i_4_theories_quantifiees.i_4_3_tactiques_abrege_quantif import (
    existe_elimination, alpha_existe, alpha_pour_tout,
)
from bourbaki.ii_theorie_des_ensembles.ii_1_relations_collectivisantes.ensembles_theoremes import (
    extensionnalite_appliquee,
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
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_unicite_essai_rec import (
    dom_essai_inclus_E,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_coincidence_famille import (
    point_dans_dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    couverture_totale_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_capstone_rec import (
    Dglob_rec, membre_Dglob_rec,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def dom_f_inclus_E(vh, G="Gsr", e="Esr", V="Vval"):
    """⊢ dom(⋃Dglob_rec) ⊂ E                                  [CLOS, 0 hyp]."""
    vG, ve = _t(G), _t(e)
    D = Dglob_rec(vG, ve, V)
    f = union_famille(D)
    vz, vw, vpun, vy = var("zge"), var("wge"), var("punion"), var("yDg")

    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)
    h_z = N.assume(appartient(vz, E.dom(f)))
    ex_w = N.modus_ponens(
        N.modus_ponens(h_z, equivalence_avant(instancie(instancie(ax_dom, f), vz))),
        equivalence_avant(alpha_existe("y", "wge",
                                       appartient(E.couple(vz, var("y")), f))))
    h_zw = N.assume(appartient(E.couple(vz, vw), f))
    ex_pun = N.modus_ponens(h_zw, equivalence_avant(
        _inst_union_famille(D, E.couple(vz, vw))))
    corps_pun = et(appartient(vpun, D), appartient(E.couple(vz, vw), vpun))
    h_pun = N.assume(corps_pun)
    sel = conjonction_elim_droite(N.modus_ponens(
        conjonction_elim_gauche(h_pun),
        equivalence_avant(membre_Dglob_rec(vh, G, e, vpun, V, y="yDg"))))
    corps_y = et(appartient(vy, ve), est_essai_rec(vpun, vh, vG, ve, vy))
    h_y = N.assume(corps_y)
    y_E = conjonction_elim_gauche(h_y)
    dom_pun = conjonction_elim_droite(conjonction_elim_gauche(
        conjonction_elim_droite(h_y)))                      # dom punion = dom_essai(yDg)
    z_dey = N.modus_ponens(
        _cut(conjonction_elim_droite(h_pun), appartient(E.couple(vz, vw), vpun),
             couple_dans_dom(vpun, vz, vw)),
        equivalence_avant(N.modus_ponens(dom_pun, N.s6(
            E.dom(vpun), dom_essai(vG, ve, vy), "wdz", appartient(vz, var("wdz"))))))
    incl_E = _cut(y_E, appartient(vy, ve), dom_essai_inclus_E(G, e, "yDg"))
    z_E = N.modus_ponens(z_dey, instancie(incl_E, vz))
    r1 = N.modus_ponens(sel, existe_elimination(
        N.loi_deduction(corps_y, z_E), "yDg"))
    r2 = N.modus_ponens(ex_pun, existe_elimination(
        N.loi_deduction(corps_pun, r1), "punion"))
    r3 = N.modus_ponens(ex_w, existe_elimination(
        N.loi_deduction(appartient(E.couple(vz, vw), f), r2), "wge"))
    sub = N.loi_deduction(appartient(vz, E.dom(f)), r3)
    res = N.modus_ponens(N.generalisation("zge", sub), equivalence_avant(
        alpha_pour_tout("zge", "z", impl(appartient(vz, E.dom(f)),
                                         appartient(vz, ve)))))
    assert res.est_clos, "dom_f_inclus_E : non clos"
    return res


def E_inclus_dom_f(vh, G="Gsr", e="Esr", V="Vval"):
    """{ bo, regle_dans_V } ⊢ E ⊂ dom(⋃Dglob_rec)             [2 hyps honnêtes]."""
    vG, ve = _t(G), _t(e)
    D = Dglob_rec(vG, ve, V)
    f = union_famille(D)
    vz, vpa = var("zge"), var("paa")
    ax_dom = N.axiome(E.theorie_ensembles(), E.AXIOME_DOM)

    cov = couverture_totale_rec(vh, G, e, V)                # {bo, règle}
    h_z = N.assume(appartient(vz, ve))
    cov_z = N.modus_ponens(h_z, instancie(cov, vz))
    corps_pa = et(appartient(vpa, ambiant(e, V)),
                  est_essai_rec(vpa, vh, vG, ve, vz))
    h_pa = N.assume(corps_pa)
    pa_amb = conjonction_elim_gauche(h_pa)
    essai_pa = conjonction_elim_droite(h_pa)
    func_pa = conjonction_elim_gauche(conjonction_elim_gauche(essai_pa))
    dom_pa = conjonction_elim_droite(conjonction_elim_gauche(essai_pa))
    # paa ∈ Dglob (témoin S5 : z lui-même, qui est dans E)
    inner = et(appartient(var("yDg"), ve),
               est_essai_rec(vpa, vh, vG, ve, var("yDg")))
    ex_y = N.modus_ponens(conjonction_intro(h_z, essai_pa),
                          N.s5(inner, vz, "yDg"))
    pa_D = N.modus_ponens(conjonction_intro(pa_amb, ex_y), equivalence_arriere(
        membre_Dglob_rec(vh, G, e, vpa, V, y="yDg")))
    # z ∈ dom paa, puis (z, paa(z)) ∈ paa ⊂ f
    z_dompa = N.modus_ponens(point_dans_dom_essai(G, e, "zge"),
        equivalence_arriere(N.modus_ponens(dom_pa, N.s6(
            E.dom(vpa), dom_essai(vG, ve, vz), "wdz", appartient(vz, var("wdz"))))))
    ex_y0 = N.modus_ponens(z_dompa, equivalence_avant(
        instancie(instancie(ax_dom, vpa), vz)))
    zin = _cut(ex_y0, existe("y", appartient(E.couple(vz, var("y")), vpa)),
               _cut(func_pa, E.est_fonctionnel(vpa), valeur_dans_graphe(vpa, vz)))
    in_f = _membre_dans_union(D, vpa, E.couple(vz, E.valeur(vpa, vz)), pa_D, zin)
    ex_y2 = N.modus_ponens(in_f, N.s5(
        appartient(E.couple(vz, var("y")), f), E.valeur(vpa, vz), "y"))
    z_domf = N.modus_ponens(ex_y2, equivalence_arriere(
        instancie(instancie(ax_dom, f), vz)))
    r = N.modus_ponens(cov_z, existe_elimination(
        N.loi_deduction(corps_pa, z_domf), "paa"))
    sub = N.loi_deduction(appartient(vz, ve), r)
    return N.modus_ponens(N.generalisation("zge", sub), equivalence_avant(
        alpha_pour_tout("zge", "z", impl(appartient(vz, ve),
                                         appartient(vz, E.dom(f))))))


def dom_f_egal_E(vh, G="Gsr", e="Esr", V="Vval"):
    """🎯 { bo, regle_dans_V } ⊢ dom(⋃Dglob_rec) = E          [2 hyps honnêtes]."""
    vG, ve = _t(G), _t(e)
    f = union_famille(Dglob_rec(vG, ve, V))
    res = N.modus_ponens(
        conjonction_intro(dom_f_inclus_E(vh, G, e, V), E_inclus_dom_f(vh, G, e, V)),
        extensionnalite_appliquee(E.dom(f), ve))
    assert res.conclusion == egal(E.dom(f), ve), "dom_f_egal_E : forme"
    assert len(res.hypotheses) == 2, "dom_f_egal_E : hyps ≠ 2"
    return res


__all__ = ["dom_f_inclus_E", "E_inclus_dom_f", "dom_f_egal_E"]
