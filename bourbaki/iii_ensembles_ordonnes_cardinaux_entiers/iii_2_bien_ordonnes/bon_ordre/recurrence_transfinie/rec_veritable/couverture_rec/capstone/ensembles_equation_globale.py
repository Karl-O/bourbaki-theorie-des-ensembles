# -*- coding: utf-8 -*-
"""§III.2.2 — R7' (étape 3) : L'ÉQUATION DE RÉCURSION VAUT PARTOUT SUR f.

🎯 CIBLES (f := ⋃Dglob_rec(G,E,V)) :

    seg_inclus_E :  ⊢ seg(G,E,x) ⊂ E                           [CLOS, 0 hyp]
    equation_f   :  { bo, regle_dans_V }
                    ⊢ (∀z)( z∈dom f ⇒ f(z) = vh( f|seg z ) )

Le patron U4 (equation_union_rec) porté au GLOBAL : le témoin paa vient de la
COUVERTURE TOTALE (R6') au lieu de l'antécédent d'induction, et les inclusions
de domaine passent par dom f = E (étape 2) au lieu de dom ⋃D = seg(x).

theorie_ensembles() INCHANGÉE (22).  Noyau INTACT.  vh OPAQUE (callable).
"""
from __future__ import annotations

from bourbaki.i_description_mathematique_formelle.i_1_termes_relations.outil_formule import (
    Terme, var, egal, et, impl, appartient, inclus,
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
from bourbaki.i_description_mathematique_formelle.i_5_theories_egalitaires.i_5_2_tactiques_abrege_egalite import (
    symetrie, composer_egalites, congruence_terme,
)
from bourbaki.ii_theorie_des_ensembles.ii_3_correspondances.ii_3_4_fonctions.ensembles_extensionnalite import (
    graphe_egal_par_valeurs,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_equipotence_cardinaux.cantor_bernstein.ensembles_cantor_bernstein_bij import (
    restriction_dom_sous_inclusion, restriction_valeur, _restriction_fonctionnelle_terme,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_3_3_operations_cardinaux.iii_3_6_familles.ensembles_produit_adjonction_briques import (
    restriction_est_graphe,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_coeur import (
    union_famille, famille_compatible, union_famille_fonctionnelle,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_seg_transitif import (
    seg_inclus_dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_assemblage import (
    equation_sur_seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_coincidence_famille import (
    point_dans_dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_equation_union import (
    _transfert_valeur,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_heredite_rec import (
    couverture_totale_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_capstone_rec import (
    Dglob_rec, membre_Dglob_rec, compatibilite_Dglob,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.capstone.ensembles_domaine_global import (
    dom_f_inclus_E, dom_f_egal_E,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def seg_inclus_E(G="Gsr", e="Esr", x="xsr", u="use"):
    """⊢ seg(G,E,x) ⊂ E   (conjoint gauche-gauche de l'axiome-segment ; CLOS)."""
    vG, ve, vx, vu = _t(G), _t(e), _t(x), var(u)
    segx = E.segment_extremite(vG, ve, vx)
    ax_seg = instancie(N.axiome(E.theorie_segment_extremite(),
                                E.axiome_segment_extremite()), vG)
    h_u = N.assume(appartient(vu, segx))
    u_E = conjonction_elim_gauche(conjonction_elim_gauche(N.modus_ponens(
        h_u, equivalence_avant(instancie(instancie(instancie(ax_seg, ve), vx), vu)))))
    gen = N.generalisation(u, N.loi_deduction(appartient(vu, segx), u_E))
    res = N.modus_ponens(gen, equivalence_avant(alpha_pour_tout(
        u, "z", impl(appartient(vu, segx), appartient(vu, ve)))))
    assert res.est_clos, "seg_inclus_E : non clos"
    return res


def equation_f(vh, G="Gsr", e="Esr", V="Vval"):
    """🎯 R7'-étape 3 : { bo, regle_dans_V } ⊢ equation_sur_seg(f, vh, G, E)."""
    vG, ve = _t(G), _t(e)
    D = Dglob_rec(vG, ve, V)
    f = union_famille(D)
    vz, vpa = var("zesr"), var("paa")
    segz = E.segment_extremite(vG, ve, vz)
    rF = E.restriction(f, segz)
    rPa = E.restriction(vpa, segz)

    compat = compatibilite_Dglob(vh, G, e, V)               # {bo}
    fc = famille_compatible(D)
    func_f = _cut(compat, fc, union_famille_fonctionnelle(D))

    h_z = N.assume(appartient(vz, E.dom(f)))
    z_E = N.modus_ponens(h_z, instancie(dom_f_inclus_E(vh, G, e, V), vz))
    cov_z = N.modus_ponens(z_E, instancie(couverture_totale_rec(vh, G, e, V), vz))
    corps_pa = et(appartient(vpa, ambiant(e, V)),
                  est_essai_rec(vpa, vh, vG, ve, vz))
    h_pa = N.assume(corps_pa)
    pa_amb = conjonction_elim_gauche(h_pa)
    essai_pa = conjonction_elim_droite(h_pa)
    func_pa = conjonction_elim_gauche(conjonction_elim_gauche(essai_pa))
    dom_pa = conjonction_elim_droite(conjonction_elim_gauche(essai_pa))
    eq_pa = conjonction_elim_droite(essai_pa)

    # paa∈Dglob  (témoin S5 : z, qui est dans E)
    inner = et(appartient(var("yDg"), ve),
               est_essai_rec(vpa, vh, vG, ve, var("yDg")))
    ex_y = N.modus_ponens(conjonction_intro(z_E, essai_pa),
                          N.s5(inner, vz, "yDg"))
    pa_D = N.modus_ponens(conjonction_intro(pa_amb, ex_y), equivalence_arriere(
        membre_Dglob_rec(vh, G, e, vpa, V, y="yDg")))
    z_dompa = N.modus_ponens(point_dans_dom_essai(G, e, "zesr"),
        equivalence_arriere(N.modus_ponens(dom_pa, N.s6(
            E.dom(vpa), dom_essai(vG, ve, vz), "weu", appartient(vz, var("weu"))))))

    # (a) f(z) = paa(z) ; (b) paa(z) = vh(paa|seg z)
    vuf = _cut(compat, fc, _transfert_valeur(D, vpa, pa_D, vz, z_dompa))
    eq_z = N.modus_ponens(z_dompa, instancie(eq_pa, vz))

    # (c) paa|seg z = f|seg z  (extensionnalité)
    sid = N.modus_ponens(point_dans_dom_essai(G, e, "zesr"),
                         seg_inclus_dom_essai(G, e, "zesr", "zesr"))
    sub_dompa = N.modus_ponens(sid, equivalence_avant(N.modus_ponens(
        N.modus_ponens(dom_pa, symetrie(E.dom(vpa), dom_essai(vG, ve, vz))),
        N.s6(dom_essai(vG, ve, vz), E.dom(vpa), "weu", inclus(segz, var("weu"))))))
    df = dom_f_egal_E(vh, G, e, V)                          # {bo, règle} dom f=E
    sub_domf = N.modus_ponens(seg_inclus_E(G, e, "zesr"), equivalence_avant(
        N.modus_ponens(N.modus_ponens(df, symetrie(E.dom(f), ve)),
                       N.s6(ve, E.dom(f), "weu", inclus(segz, var("weu"))))))
    d_pa = N.modus_ponens(sub_dompa, restriction_dom_sous_inclusion(vpa, segz))
    d_f = N.modus_ponens(sub_domf, restriction_dom_sous_inclusion(f, segz))
    dom_eq = composer_egalites(d_pa, N.modus_ponens(d_f, symetrie(E.dom(rF), segz)))
    f_pa = N.modus_ponens(func_pa, _restriction_fonctionnelle_terme(vpa, segz))
    f_f = N.modus_ponens(func_f, _restriction_fonctionnelle_terme(f, segz))
    g_pa = restriction_est_graphe(vpa, segz)
    g_f = restriction_est_graphe(f, segz)
    vt = var("x")
    h_t = N.assume(appartient(vt, E.dom(rPa)))
    t_segz = N.modus_ponens(h_t, equivalence_avant(N.modus_ponens(
        d_pa, N.s6(E.dom(rPa), segz, "weu", appartient(vt, var("weu"))))))
    t_dompa = N.modus_ponens(t_segz, instancie(sub_dompa, vt))
    t_domf = N.modus_ponens(t_segz, instancie(sub_domf, vt))
    rv_pa = restriction_valeur(vpa, segz, vt)
    rv_pa = _cut(t_segz, appartient(vt, segz), rv_pa)
    rv_pa = _cut(t_dompa, appartient(vt, E.dom(vpa)), rv_pa)
    rv_pa = _cut(func_pa, E.est_fonctionnel(vpa), rv_pa)
    vuf_t = _cut(compat, fc, _transfert_valeur(D, vpa, pa_D, vt, t_dompa))
    pa_f_t = N.modus_ponens(vuf_t, symetrie(E.valeur(f, vt), E.valeur(vpa, vt)))
    rv_f = restriction_valeur(f, segz, vt)
    rv_f = _cut(t_segz, appartient(vt, segz), rv_f)
    rv_f = _cut(t_domf, appartient(vt, E.dom(f)), rv_f)
    rv_f = _cut(func_f, E.est_fonctionnel(f), rv_f)
    chaine_t = composer_egalites(composer_egalites(rv_pa, pa_f_t),
        N.modus_ponens(rv_f, symetrie(E.valeur(rF, vt), E.valeur(f, vt))))
    val_eq = N.generalisation("x",
        N.loi_deduction(appartient(vt, E.dom(rPa)), chaine_t))
    prem = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(f_pa, f_f), g_pa), g_f), dom_eq), val_eq)
    cong = N.modus_ponens(N.modus_ponens(prem, graphe_egal_par_valeurs(rPa, rF)),
        congruence_terme(rPa, rF, vh(var("wrec")), "wrec"))

    # (d) f(z) = paa(z) = vh(paa|seg z) = vh(f|seg z) ; élimination du témoin
    chaine_z = composer_egalites(composer_egalites(vuf, eq_z), cong)
    r = N.modus_ponens(cov_z, existe_elimination(
        N.loi_deduction(corps_pa, chaine_z), "paa"))
    res = N.generalisation("zesr",
        N.loi_deduction(appartient(vz, E.dom(f)), r))

    assert res.conclusion == equation_sur_seg(f, vh, vG, ve), "equation_f : forme"
    assert len(res.hypotheses) == 2, "equation_f : hyps ≠ 2"
    return res


__all__ = ["seg_inclus_E", "equation_f"]
