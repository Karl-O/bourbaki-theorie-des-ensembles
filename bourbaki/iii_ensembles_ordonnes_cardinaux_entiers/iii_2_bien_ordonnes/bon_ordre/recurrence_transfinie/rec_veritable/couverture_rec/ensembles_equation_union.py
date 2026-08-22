# -*- coding: utf-8 -*-
"""§III.2.2 — R5'c (U4) : L'ÉQUATION DE RÉCURSION PASSE À LA RÉUNION.

🎯 CIBLE (deux hypothèses honnêtes) :

    equation_union_rec :
        { bo, antécédent }  ⊢  (∀z)( z∈dom(⋃D) ⇒ (⋃D)(z) = vh( (⋃D)|seg z ) )

où D = Dfam_rec(x) et l'antécédent est la couverture-ambiante des y<x.
C'est la forme EXACTE `equation_sur_seg` attendue par extension_essai_rec (R3') :
la réunion des essais est un ESSAI-SUR-SEG, prête au prolongement.

PREUVE.  z∈dom(⋃D) ⊂ seg(x) (U2) est couvert (antécédent) par un essai paa en z :
  (⋃D)(z) = paa(z)                [valeur_union_famille, compat U1]
          = vh( paa|seg z )       [l'équation de l'essai paa]
          = vh( (⋃D)|seg z )      [paa|seg z = (⋃D)|seg z + congruence C44].
L'égalité des restrictions est une extensionnalité (graphe_egal_par_valeurs) :
mêmes domaines (seg z ⊂ dom paa par point_dans+brique (ii) ; seg z ⊂ dom(⋃D)
par seg_inclus_seg + U-dom), mêmes valeurs (valeur_union_famille en chaque u).

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
    valeur_union_famille,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_realisation import (
    ambiant,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.ensembles_c60_existence_close import dom_essai
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_essai_rec import (
    est_essai_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_seg_transitif import (
    seg_transitif_strict, seg_inclus_dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.ensembles_extension_assemblage import (
    equation_sur_seg,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_coincidence_famille import (
    point_dans_dom_essai,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_famille_rec import (
    Dfam_rec, membre_Dfam_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_union_rec import (
    compatibilite_Dfam_rec,
)
from bourbaki.iii_ensembles_ordonnes_cardinaux_entiers.iii_2_bien_ordonnes.bon_ordre.recurrence_transfinie.rec_veritable.couverture_rec.ensembles_domaine_union import (
    antecedent_couverture_rec, dom_union_inclus_seg, dom_union_rec,
)


def _t(t):
    """Coercion str/Terme → Terme."""
    return t if isinstance(t, Terme) else var(t)


def _cut(preuve, formule, thm):
    """Décharge l'hypothèse `formule` de `thm` par la preuve `preuve` (coupure)."""
    return N.modus_ponens(preuve, N.loi_deduction(formule, thm))


def _transfert_valeur(D, membre, membre_D, point, point_dom):
    """{famille_compatible(D)} + preuves(membre∈D, point∈dom membre)
       ⊢ (⋃D)(point) = membre(point)   — pour des TERMES.

    valeur_union_famille réutilise son paramètre p comme LIEUR de
    famille_compatible : passer un Terme y fabriquerait un lieur malformé
    (leçon var-sur-Terme).  On l'appelle donc aux NOMS par défaut, on décharge
    ses deux hypothèses à noms, on ∀-clôt sur pcf/u (LIÉS dans la
    compatibilité, donc légal) et on instancie aux termes — patron keystone."""
    vuf = valeur_union_famille(D)                           # p="pcf", u="u"
    imp = N.loi_deduction(appartient(var("pcf"), D),
          N.loi_deduction(appartient(var("u"), E.dom(var("pcf"))), vuf))
    gen = N.generalisation("pcf", N.generalisation("u", imp))
    inst = instancie(instancie(gen, membre), point)
    return N.modus_ponens(point_dom, N.modus_ponens(membre_D, inst))


def seg_inclus_seg(G="Gsr", e="Esr", x="xsr", z="zeu", u="ueu"):
    """{ bo, z∈seg(x) } ⊢ seg(z) ⊂ seg(x)   (transitivité stricte généralisée)."""
    vG, ve, vx, vz, vu = _t(G), _t(e), _t(x), _t(z), var(u)
    segx = E.segment_extremite(vG, ve, vx)
    segz = E.segment_extremite(vG, ve, vz)
    h_zs = N.assume(appartient(vz, segx))
    h_u = N.assume(appartient(vu, segz))
    u_segx = N.modus_ponens(conjonction_intro(h_zs, h_u),
                            seg_transitif_strict(G, e, x, z, u))
    gen = N.generalisation(u, N.loi_deduction(appartient(vu, segz), u_segx))
    return N.modus_ponens(gen, equivalence_avant(alpha_pour_tout(
        u, "z", impl(appartient(vu, segz), appartient(vu, segx)))))


def equation_union_rec(vh, G="Gsr", e="Esr", x="xsr", V="Vval"):
    """🎯 U4 : { bo, antécédent } ⊢ equation_sur_seg(⋃Dfam_rec(x), vh, G, E)."""
    vG, ve, vx = _t(G), _t(e), _t(x)
    D = Dfam_rec(vG, ve, vx, V)
    U = union_famille(D)
    segx = E.segment_extremite(vG, ve, vx)
    vz, vpa = var("zesr"), var("paa")
    segz = E.segment_extremite(vG, ve, vz)
    rU = E.restriction(U, segz)
    rPa = E.restriction(vpa, segz)

    compat = compatibilite_Dfam_rec(vh, G, e, x, V)         # {bo}
    fc = famille_compatible(D)
    func_U = _cut(compat, fc, union_famille_fonctionnelle(D))   # {bo} func(⋃D)

    h_ant = N.assume(antecedent_couverture_rec(vh, G, e, x, V))
    h_z = N.assume(appartient(vz, E.dom(U)))
    z_segx = N.modus_ponens(h_z,
        instancie(dom_union_inclus_seg(vh, G, e, x, V), vz))    # z∈seg(x)  {bo}
    cov_z = N.modus_ponens(z_segx, instancie(h_ant, vz))
    corps_pa = et(appartient(vpa, ambiant(e, V)),
                  est_essai_rec(vpa, vh, vG, ve, vz))
    h_pa = N.assume(corps_pa)
    pa_amb = conjonction_elim_gauche(h_pa)
    essai_pa = conjonction_elim_droite(h_pa)
    func_pa = conjonction_elim_gauche(conjonction_elim_gauche(essai_pa))
    dom_pa = conjonction_elim_droite(conjonction_elim_gauche(essai_pa))
    eq_pa = conjonction_elim_droite(essai_pa)

    # paa∈D  (témoin S5 : z lui-même — patron U3)
    inner = et(appartient(var("yDr"), segx),
               est_essai_rec(vpa, vh, vG, ve, var("yDr")))
    ex_yDr = N.modus_ponens(conjonction_intro(z_segx, essai_pa),
                            N.s5(inner, vz, "yDr"))
    pa_D = N.modus_ponens(conjonction_intro(pa_amb, ex_yDr), equivalence_arriere(
        membre_Dfam_rec(vh, G, e, vx, vpa, V, y="yDr")))
    # z∈dom paa  (le point est dans son dom_essai)
    z_dompa = N.modus_ponens(point_dans_dom_essai(G, e, "zesr"),
        equivalence_arriere(N.modus_ponens(dom_pa, N.s6(
            E.dom(vpa), dom_essai(vG, ve, vz), "weu", appartient(vz, var("weu"))))))

    # (a) U(z) = paa(z)   (transfert de valeur, version termes)
    vuf = _cut(compat, fc, _transfert_valeur(D, vpa, pa_D, vz, z_dompa))
    # (b) paa(z) = vh(paa|seg z)
    eq_z = N.modus_ponens(z_dompa, instancie(eq_pa, vz))

    # (c) paa|seg z = U|seg z  (extensionnalité fonctionnelle)
    #   seg z ⊂ dom paa
    sid = N.modus_ponens(point_dans_dom_essai(G, e, "zesr"),
                         seg_inclus_dom_essai(G, e, "zesr", "zesr"))  # {bo}
    sub_dompa = N.modus_ponens(sid, equivalence_avant(N.modus_ponens(
        N.modus_ponens(dom_pa, symetrie(E.dom(vpa), dom_essai(vG, ve, vz))),
        N.s6(dom_essai(vG, ve, vz), E.dom(vpa), "weu", inclus(segz, var("weu"))))))
    #   seg z ⊂ dom U   (seg z ⊂ seg x = dom U)
    sis = _cut(z_segx, appartient(vz, segx), seg_inclus_seg(G, e, x, "zesr"))
    du = dom_union_rec(vh, G, e, x, V)                      # {bo, ant} dom U=seg x
    sub_domU = N.modus_ponens(sis, equivalence_avant(N.modus_ponens(
        N.modus_ponens(du, symetrie(E.dom(U), segx)),
        N.s6(segx, E.dom(U), "weu", inclus(segz, var("weu"))))))
    #   domaines, fonctionnalités, graphes
    d_pa = N.modus_ponens(sub_dompa, restriction_dom_sous_inclusion(vpa, segz))
    d_U = N.modus_ponens(sub_domU, restriction_dom_sous_inclusion(U, segz))
    dom_eq = composer_egalites(d_pa, N.modus_ponens(d_U, symetrie(E.dom(rU), segz)))
    f_pa = N.modus_ponens(func_pa, _restriction_fonctionnelle_terme(vpa, segz))
    f_U = N.modus_ponens(func_U, _restriction_fonctionnelle_terme(U, segz))
    g_pa = restriction_est_graphe(vpa, segz)
    g_U = restriction_est_graphe(U, segz)
    #   valeurs (lieur « x » imposé par l'extensionnalité)
    vt = var("x")
    h_t = N.assume(appartient(vt, E.dom(rPa)))
    t_segz = N.modus_ponens(h_t, equivalence_avant(N.modus_ponens(
        d_pa, N.s6(E.dom(rPa), segz, "weu", appartient(vt, var("weu"))))))
    t_dompa = N.modus_ponens(t_segz, instancie(sub_dompa, vt))
    t_domU = N.modus_ponens(t_segz, instancie(sub_domU, vt))
    rv_pa = restriction_valeur(vpa, segz, vt)
    rv_pa = _cut(t_segz, appartient(vt, segz), rv_pa)
    rv_pa = _cut(t_dompa, appartient(vt, E.dom(vpa)), rv_pa)
    rv_pa = _cut(func_pa, E.est_fonctionnel(vpa), rv_pa)    # (paa|segz)(t)=paa(t)
    vuf_t = _cut(compat, fc, _transfert_valeur(D, vpa, pa_D, vt, t_dompa))
    pa_U_t = N.modus_ponens(vuf_t, symetrie(E.valeur(U, vt), E.valeur(vpa, vt)))
    rv_U = restriction_valeur(U, segz, vt)
    rv_U = _cut(t_segz, appartient(vt, segz), rv_U)
    rv_U = _cut(t_domU, appartient(vt, E.dom(U)), rv_U)
    rv_U = _cut(func_U, E.est_fonctionnel(U), rv_U)         # (U|segz)(t)=U(t)
    chaine_t = composer_egalites(composer_egalites(rv_pa, pa_U_t),
        N.modus_ponens(rv_U, symetrie(E.valeur(rU, vt), E.valeur(U, vt))))
    val_eq = N.generalisation("x",
        N.loi_deduction(appartient(vt, E.dom(rPa)), chaine_t))
    prem = conjonction_intro(conjonction_intro(conjonction_intro(conjonction_intro(
        conjonction_intro(f_pa, f_U), g_pa), g_U), dom_eq), val_eq)
    restr_eq = N.modus_ponens(prem, graphe_egal_par_valeurs(rPa, rU))
    cong = N.modus_ponens(restr_eq, congruence_terme(
        rPa, rU, vh(var("wrec")), "wrec"))                  # vh(paa|segz)=vh(U|segz)

    # (d) U(z) = paa(z) = vh(paa|seg z) = vh(U|seg z) ; élimination du témoin
    chaine_z = composer_egalites(composer_egalites(vuf, eq_z), cong)
    r = N.modus_ponens(cov_z, existe_elimination(
        N.loi_deduction(corps_pa, chaine_z), "paa"))
    res = N.generalisation("zesr",
        N.loi_deduction(appartient(vz, E.dom(U)), r))

    cible = equation_sur_seg(U, vh, vG, ve)
    assert res.conclusion == cible, "equation_union_rec : ≠ equation_sur_seg(⋃D)"
    assert len(res.hypotheses) == 2, "equation_union_rec : hyps ≠ 2"
    return res


__all__ = ["seg_inclus_seg", "equation_union_rec"]
